Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common ListSupport FMap Syntax Semantics SemFacts StepDet StepSeq Serial.

Set Implicit Arguments.

Lemma transactional_cons_inv:
  forall sys a ll,
    Transactional sys (a :: ll) ->
    Transactional sys ll.
Proof.
  unfold Transactional; intros.
  destruct H; [discriminate|].
  destruct H as [pmin [pmouts [? ?]]].
  remember (a :: ll) as all; inv H0; [inv H2; auto|].
  inv H4.
  right; eauto.
Qed.

Corollary transactional_ocons_inv:
  forall sys oa ll,
    Transactional sys (oa ::> ll) ->
    Transactional sys ll.
Proof.
  destruct oa as [a|]; simpl; intros; auto.
  eauto using transactional_cons_inv.
Qed.

Lemma steps_seq_atomic_tid:
  forall sys st1 ll st2,
    steps step_seq sys st1 ll st2 ->
    forall ts,
      tst_tid st2 = ts ->
      forall tmsg min mouts,
        Atomic min ll mouts ->
        In tmsg mouts ->
        tmsg_tid tmsg = ts.
Proof.
  induction 1; simpl; intros; [inv H0|].
  inv H2.
  - eauto using step_seq_outs_tid.
  - apply in_app_or in H3; destruct H3.
    + eapply IHsteps; eauto.
      * eauto using step_seq_internal_tid_intact.
      * eauto using in_remove.
    + eapply step_seq_outs_tid; eauto.
Qed.

Lemma transactional_steps_seq:
  forall sys ll,
    Transactional sys ll ->
    forall st1 st2,
      steps step_det sys st1 ll st2 ->
      steps step_seq sys st1 ll st2.
Proof.
  induction ll as [|l ll]; simpl; intros; subst; [inv H0; constructor|].

  (* NOTE: [l] is the youngest label. *)
  inv H0.
  specialize (IHll (transactional_cons_inv H) _ _ H4).
  destruct l.

  - (* IlblExt *)
    inv H; [discriminate|].
    destruct H0 as [trin [trouts [? ?]]].
    inv H6.
    econstructor; [eassumption|].
    econstructor; eauto.

  - (* IlblInt *)
    inv H; [discriminate|].
    destruct H0 as [trin [trouts [? ?]]].
    inv H6; [inv H0; discriminate|].
    econstructor; [eassumption|].
    econstructor; eauto.
    inv H0.
    eauto using steps_seq_atomic_tid.
Qed.

Lemma sequential_steps':
  forall sys trs,
    Forall (Transactional sys) trs ->
    forall ll,
      ll = concat trs ->
      forall st,
        steps step_det sys (getStateInit sys) ll st ->
        steps step_seq sys (getStateInit sys) ll st.
Proof.
  induction trs; intros.

  - simpl in H0; subst.
    inv H1; constructor.

  - inv H.
    specialize (IHtrs H5); clear H5.
    simpl in H1.
    eapply steps_split in H1; [|reflexivity].
    destruct H1 as [sti [? ?]].
    specialize (IHtrs _ eq_refl _ H); clear H.
    pose proof (transactional_steps_seq H4 H0).
    simpl; eauto using steps_append.
Qed.

Lemma sequential_steps:
  forall sys ll,
    Sequential sys ll ->
    forall st,
      steps step_det sys (getStateInit sys) ll st ->
      steps step_seq sys (getStateInit sys) ll st.
Proof.
  unfold Sequential; intros.
  destruct H as [trs [? ?]]; subst.
  eauto using sequential_steps'.
Qed.

Theorem serializable_step_seq:
  forall sys ll st,
    steps step_det sys (getStateInit sys) ll st ->
    Serializable sys step_det ll ->
    Behavior step_seq sys (behaviorOf ll).
Proof.
  unfold Serializable; intros.
  destruct H0 as [sll [sst [? [? ?]]]].
  pose proof (sequential_steps H1 H0) as Hseq.
  eapply Behv; eauto.
  destruct H2; assumption.
Qed.

Theorem sequential_step_seq:
  forall sys,
    Serial sys step_det -> step_det # step_seq |-- sys ⊑[id] sys.
Proof.
  unfold Serial, Refines; intros.
  inv H0; rename ll0 into ill. (* ill: the interleaving label sequence *)
  specialize (H _ _ H1).
  rewrite map_id.
  eauto using serializable_step_seq.
Qed.

