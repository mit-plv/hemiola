Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepDet StepSeq.

Lemma internal_not_external:
  forall sys idx,
    isInternal sys idx = true -> isExternal sys idx = false.
Proof.
  unfold isInternal, isExternal; intros.
  find_if_inside; auto.
Qed.

Lemma external_not_internal:
  forall sys idx,
    isExternal sys idx = true -> isInternal sys idx = false.
Proof.
  unfold isInternal, isExternal; intros.
  find_if_inside; auto.
Qed.

Lemma internal_external_false:
  forall sys idx,
    isInternal sys idx = true -> isExternal sys idx = true -> False.
Proof.
  unfold isInternal, isExternal; intros.
  find_if_inside; intuition.
Qed.
  
Lemma step_det_int_internal:
  forall sys st1 hdl outs st2,
    step_det sys st1 (IlblInt (Some hdl) outs) st2 ->
    isInternal sys (mid_to (msg_id (getMsg hdl))) = true.
Proof.
  intros; inv H.
  destruct hdl as [hmid hmv]; simpl in *; subst.
  destruct H6 as [? [? ?]]; simpl in *; subst.
  rewrite H0.
  unfold isInternal; find_if_inside; auto.
  elim n; apply in_map; assumption.
Qed.

Lemma step_det_outs_internal:
  forall sys st1 ilbl st2,
    step_det sys st1 ilbl st2 ->
    Forall (fun m: TMsg => isInternal sys (mid_from (msg_id (getMsg m))) = true)
           (iLblOuts ilbl).
Proof.
  intros; inv H.
  - constructor.
  - simpl.
    apply Forall_filter.
    destruct H11.
    clear -H H0.
    remember (pmsg_outs _ _ _) as outs; clear Heqouts.
    induction outs; simpl; intros; [constructor|].
    inv H; dest.
    constructor; auto.
    simpl; simpl in H; unfold id in H; rewrite H.
    unfold isInternal; find_if_inside; auto.
    elim n; apply in_map; assumption.
  - simpl.
    apply Forall_filter.
    destruct H9.
    clear -H H0.
    remember (pmsg_outs _ _ _) as outs; clear Heqouts.
    induction outs; simpl; intros; [constructor|].
    inv H; dest.
    constructor; auto.
    simpl; simpl in H; unfold id in H; rewrite H.
    unfold isInternal; find_if_inside; auto.
    elim n; apply in_map; assumption.
Qed.

Lemma step_seq_tid:
  forall sys ats1 l ats2,
    step_seq sys ats1 l ats2 ->
    forall hdl,
      iLblHdl l = Some hdl ->
      Forall (fun tmsg => tmsg_tid tmsg = tmsg_tid hdl) (iLblOuts l).
Proof.
  intros; inv H.
  - discriminate.
  - simpl in H0; inv H0.
    clear; simpl.
    induction (pmsg_outs _ _ _); simpl; auto.
    find_if_inside; auto.
  - simpl in H0; inv H0.
    clear; simpl.
    induction (pmsg_outs _ _ _); simpl; auto.
    find_if_inside; auto.
Qed.

Lemma step_seq_outs_tid:
  forall sys st1 l st2,
    step_seq sys st1 l st2 ->
    forall tmsg,
      In tmsg (iLblOuts l) ->
      tmsg_tid tmsg = tst_tid st2.
Proof.
  intros; inv H.
  - inv H0.
  - simpl; simpl in H0.
    unfold extOuts in H0; apply filter_In in H0; dest.
    unfold toTMsgs in H; apply in_map_iff in H; dest.
    subst; reflexivity.
  - simpl; simpl in H0.
    unfold extOuts in H0; apply filter_In in H0; dest.
    unfold toTMsgs in H; apply in_map_iff in H; dest.
    subst; reflexivity.
Qed.

Lemma step_seq_internal_tid_intact:
  forall sys st1 hdl outs st2,
    step_seq sys st1 (IlblInt hdl outs) st2 ->
    tst_tid st1 = tst_tid st2.
Proof.
  intros; inv H; reflexivity.
Qed.

Lemma steps_split:
  forall {StateT LabelT} (step: Step StateT LabelT) sys st1 st2 ll,
    steps step sys st1 ll st2 ->
    forall ll1 ll2,
      ll = ll2 ++ ll1 ->
      exists sti,
        steps step sys st1 ll1 sti /\
        steps step sys sti ll2 st2.
Proof.
  induction 1; simpl; intros.
  - apply eq_sym, app_eq_nil in H; dest; subst.
    eexists; split; econstructor.
  - destruct ll2.
    + simpl in H1; subst.
      specialize (IHsteps ll nil eq_refl).
      destruct IHsteps as [tsi [? ?]].
      inv H2.
      eexists; split.
      * econstructor; eauto.
      * econstructor.
    + simpl in H1; inv H1.
      specialize (IHsteps _ _ eq_refl).
      destruct IHsteps as [sti [? ?]].
      eexists; split; eauto.
      econstructor; eauto.
Qed.

Lemma steps_append:
  forall {StateT LabelT} (step: Step StateT LabelT) sys st1 ll1 st2,
    steps step sys st1 ll1 st2 ->
    forall ll2 st3,
      steps step sys st2 ll2 st3 ->
      steps step sys st1 (ll2 ++ ll1) st3.
Proof.
  induction 2; simpl; intros; [auto|].
  econstructor; eauto.
Qed.

Lemma map_id:
  forall {A} (l: list A), map id l = l.
Proof.
  induction l; simpl; auto.
  rewrite IHl; reflexivity.
Qed.

Lemma map_trans:
  forall {A B C} (l: list A) (p: A -> B) (q: B -> C),
    map q (map p l) = map (fun a => q (p a)) l.
Proof.
  induction l; simpl; intros; auto.
  rewrite IHl; reflexivity.
Qed.

Theorem refines_refl:
  forall {StateT LabelT} `{HasInit StateT} `{HasLabel LabelT}
         (step: Step StateT LabelT) sys, step # step |-- sys ⊑[id] sys.
Proof.
  unfold Refines; intros.
  rewrite map_id.
  assumption.
Qed.

Theorem refines_trans:
  forall {StateT LabelT} `{HasInit StateT} `{HasLabel LabelT}
         (step1 step2 step3: Step StateT LabelT) p q s1 s2 s3,
    step1 # step2 |-- s1 ⊑[p] s2 ->
    step2 # step3 |-- s2 ⊑[q] s3 ->
    step1 # step3 |-- s1 ⊑[fun l => q (p l)] s3.
Proof.
  unfold Refines; intros.
  specialize (H2 _ (H1 _ H3)).
  rewrite map_trans in H2.
  assumption.
Qed.
  