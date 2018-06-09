Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap.
Require Import Syntax Semantics SemFacts StepM Serial Invariant.

Require Import Omega.
Require Import Program.Equality.

Set Implicit Arguments.

Section MsgParam.
  Variable MsgT: Type.
  Hypothesis (msgT_dec : forall m1 m2 : MsgT, {m1 = m2} + {m1 <> m2}).

  Lemma atomic_emptyILabel_not_in:
    forall inits ins hst outs eouts,
      Atomic msgT_dec inits ins hst outs eouts ->
      ~ In (RlblEmpty MsgT) hst.
  Proof.
    induction 1; simpl; intros.
    - intro Hx; destruct Hx; [discriminate|auto].
    - intro Hx; destruct Hx; subst; [discriminate|auto].
  Qed.

  Lemma atomic_iLblIn_not_in:
    forall inits ins hst outs eouts,
      Atomic msgT_dec inits ins hst outs eouts ->
      forall msg, ~ In (RlblIns [msg]) hst.
  Proof.
    induction 1; simpl; intros; [auto|];
      try (intro Hx; destruct Hx;
           [discriminate|firstorder]).
  Qed.

  Lemma atomic_unique:
    forall (hst: History MsgT) inits1 ins1 outs1 eouts1,
      Atomic msgT_dec inits1 ins1 hst outs1 eouts1 ->
      forall inits2 ins2 outs2 eouts2,
        Atomic msgT_dec inits2 ins2 hst outs2 eouts2 ->
        inits1 = inits2 /\ ins1 = ins2 /\
        outs1 = outs2 /\ eouts1 = eouts2.
  Proof.
    induction 1; simpl; intros; subst.
    - inv H; [auto|inv H4].
    - inv H5; [inv H|].
      specialize (IHAtomic _ _ _ _ H7).
      dest; subst; auto.
  Qed.

  Lemma atomic_messages_spec_ValidDeqs:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall sys st1 st2,
        steps step_m sys st1 hst st2 ->
        bst_msgs st2 = deqMsgs (idsOf ins) (enqMsgs outs (bst_msgs st1)) /\
        ValidDeqs (enqMsgs outs (bst_msgs st1)) (idsOf ins).
  Proof.
    induction 1; simpl; intros; subst.
    - inv H; inv H3; inv H5; simpl; split.
      + apply enqMsgs_deqMsgs_comm; auto.
      + apply ValidDeqs_enqMsgs.
        destruct H8.
        apply FirstMPI_Forall_NoDup_ValidDeqs; auto.
        
    - inv H5.
      specialize (IHAtomic _ _ _ H6); dest.
      inv H8; simpl in *; subst.
      repeat rewrite idsOf_app, deqMsgs_app, enqMsgs_app.
      split.
      + rewrite enqMsgs_deqMsgs_comm with (minds1:= idsOf rins) by assumption.
        rewrite enqMsgs_deqMsgs_ValidDeqs_comm
          with (minds:= idsOf ins) (nmsgs:= routs) by assumption.
        reflexivity.
      + apply ValidDeqs_app.
        * apply ValidDeqs_enqMsgs; auto.
        * rewrite <-enqMsgs_deqMsgs_ValidDeqs_comm
            with (minds:= idsOf ins) (nmsgs:= routs) by assumption.
          destruct H14.
          apply FirstMPI_Forall_NoDup_ValidDeqs in H13; [|assumption].
          apply ValidDeqs_enqMsgs; auto.
  Qed.

  Corollary atomic_messages_spec:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall sys st1 st2,
        steps step_m sys st1 hst st2 ->
        bst_msgs st2 = deqMsgs (idsOf ins) (enqMsgs outs (bst_msgs st1)).
  Proof.
    intros; eapply atomic_messages_spec_ValidDeqs; eauto.
  Qed.
  
  Lemma atomic_behavior_nil:
    forall {SysT} `{IsSystem SysT} (sys: SysT)
           `{HasMsg MsgT} (hst: History MsgT) inits ins outs eouts,
      Atomic msgT_dec inits ins hst outs eouts ->
      behaviorOf sys hst = nil.
  Proof.
    induction 1; simpl; intros; auto.
  Qed.

  Lemma atomic_singleton:
    forall rule ins outs,
      Atomic msgT_dec ins ins [RlblInt rule ins outs] outs outs.
  Proof.
    intros; constructor.
  Qed.

  Lemma extAtomic_preserved:
    forall impl1 (rq: Id MsgT) hst,
      ExtAtomic impl1 msgT_dec rq hst ->
      forall impl2,
        merqsOf impl1 = merqsOf impl2 ->
        ExtAtomic impl2 msgT_dec rq hst.
  Proof.
    intros.
    inv H; econstructor; eauto.
    rewrite <-H0; assumption.
  Qed.

  Lemma sequential_nil:
    forall sys, Sequential sys msgT_dec nil nil.
  Proof.
    intros; hnf; intros.
    split.
    - constructor.
    - reflexivity.
  Qed.

  Lemma sequential_silent:
    forall sys ll trss,
      Sequential sys msgT_dec ll trss ->
      Sequential sys msgT_dec (RlblEmpty _ :: ll) ([RlblEmpty _] :: trss).
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
      Sequential sys msgT_dec ll trss ->
      Sequential sys msgT_dec (RlblIns eins :: ll) ([RlblIns eins] :: trss).
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
      Sequential sys msgT_dec ll trss ->
      Sequential sys msgT_dec (RlblOuts eouts :: ll) ([RlblOuts eouts] :: trss).
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
      Sequential sys msgT_dec ll1 trss1 ->
      Sequential sys msgT_dec ll2 trss2 ->
      Sequential sys msgT_dec (ll1 ++ ll2) (trss1 ++ trss2).
  Proof.
    unfold Sequential; intros.
    destruct H, H0; subst.
    split.
    - apply Forall_app; auto.
    - apply eq_sym, concat_app.
  Qed.

  Lemma sequential_serializable:
    forall sys hst trss st,
      steps step_m sys (initsOf sys) hst st ->
      Sequential sys msg_dec hst trss ->
      Serializable sys hst.
  Proof.
    intros; red; intros.
    do 2 eexists; split.
    - split; eauto.
    - congruence.
  Qed.

  Lemma stransactional_default:
    forall lbl, STransactional msgT_dec [lbl].
  Proof.
    destruct lbl; intros.
    - eapply STrsSlt.
    - eapply STrsIns; eauto.
    - eapply STrsAtomic.
      eapply atomic_singleton.
    - eapply STrsOuts; eauto.
  Qed.

  Lemma stransactional_cons_inv:
    forall lbl (hst: History MsgT),
      STransactional msgT_dec (lbl :: hst) ->
      hst = nil \/
      STransactional msgT_dec hst.
  Proof.
    intros.
    inv H; auto.
    inv H0; auto.
    right; econstructor; eauto.
  Qed.

  Lemma ssequential_default:
    forall hst, exists n, SSequential msgT_dec hst n.
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

Lemma atomic_legal_eouts:
  forall (hst: MHistory) inits ins outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
    forall sys st1 st2,
      steps step_m sys st1 hst st2 ->
      (forall nouts,
          removeL (id_dec msg_dec) (inits ++ outs ++ nouts) ins =
          removeL (id_dec msg_dec) (inits ++ outs) ins ++ nouts) /\
      eouts = removeL (id_dec msg_dec) (inits ++ outs) ins.
Proof.
  induction 1; simpl; intros; subst.
  - split.
    + intros.
      do 2 rewrite removeL_app_2.
      reflexivity.
    + rewrite removeL_app_2; reflexivity.
  - inv H5.
    specialize (IHAtomic _ _ _ H6).
    assert (NoDup rins) by (inv H8; destruct H12; apply idsOf_NoDup; auto).
    dest; subst; split.
    + intros.
      do 2 rewrite removeL_app_1.
      rewrite <-app_assoc.
      do 2 rewrite H3.
      do 2 (rewrite removeL_app_3 with (l3:= rins) by assumption).
      apply app_assoc.
    + rewrite removeL_app_1.
      rewrite H3.
      rewrite removeL_app_3 with (l3:= rins) by assumption.
      reflexivity.
Qed.

Lemma atomic_app_SSubList:
  forall (hst1: MHistory) inits1 ins1 outs1 eouts1,
    Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
    forall hst2 inits2 ins2 outs2 eouts2,
      inits2 <> nil ->
      Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
      SubList inits2 eouts1 ->
      exists eouts,
        SSubList eouts2 eouts /\
        Atomic msg_dec inits1 (ins1 ++ ins2)
               (hst2 ++ hst1)
               (outs1 ++ outs2)
               eouts.
Proof.
  induction 3; simpl; intros.
  - eexists; split; [|econstructor; eauto].
    apply SSubList_app_1.
  - subst.
    specialize (IHAtomic H0 H7).
    destruct IHAtomic as [peouts [? ?]].

    eexists; split;
      [|apply SSubList_SubList in H4;
        do 2 rewrite app_assoc;
        econstructor; eauto;
        eapply SubList_trans; eauto].

    apply SSubList_app_2.
    apply SSubList_removeL_2; auto.
Qed.

Corollary atomic_app:
  forall (hst1: MHistory) inits1 ins1 outs1 eouts1,
    Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
    forall hst2 inits2 ins2 outs2 eouts2,
      inits2 <> nil ->
      Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
      SubList inits2 eouts1 ->
      exists eouts,
        Atomic msg_dec inits1 (ins1 ++ ins2)
               (hst2 ++ hst1)
               (outs1 ++ outs2)
               eouts.
Proof.
  intros.
  pose proof (atomic_app_SSubList H H0 H1 H2).
  dest; eauto.
Qed.

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

