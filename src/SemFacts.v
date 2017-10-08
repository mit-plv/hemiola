Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics SemDet.

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
  
Lemma step_mod_hdl_internal:
  forall sys st1 hdl outs st2,
    step_mod sys st1 (LblHdl hdl outs) st2 ->
    isInternal sys (mid_to (msg_id hdl)) = true.
Proof.
  intros; apply step_mod_step_det in H.
  inv H.
  destruct hdl as [hmid hmv]; simpl in *; subst.
  destruct H8 as [? [? ?]]; simpl in *; subst.
  rewrite H0.
  unfold isInternal; find_if_inside; auto.
  elim n; apply in_map; assumption.
Qed.

Lemma step_mod_outs_internal:
  forall sys st1 hdl outs st2,
    step_mod sys st1 (LblHdl hdl outs) st2 ->
    Forall (fun m => isInternal sys (mid_from (msg_id m)) = true) outs.
Proof.
  intros; apply step_mod_step_det in H.
  inv H.
  destruct hdl as [hmid hmv]; simpl in *; subst.
  apply Forall_filter.
  destruct H15.

  clear -H H2.
  remember (pmsg_outs _ _ _) as outs; clear Heqouts.
  induction outs; simpl; intros; [constructor|].
  inv H; dest.
  constructor; auto.
  rewrite H.
  unfold isInternal; find_if_inside; auto.
  elim n; apply in_map; assumption.
Qed.

Lemma steps_split:
  forall {MsgT} (step: Step MsgT) sys st1 st2 ll,
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
      destruct IHsteps as [sti [? ?]].
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
  forall {MsgT} (step: Step MsgT) sys st1 ll1 st2,
    steps step sys st1 ll1 st2 ->
    forall ll2 st3,
      steps step sys st2 ll2 st3 ->
      steps step sys st1 (ll2 ++ ll1) st3.
Proof.
  induction 2; simpl; intros; [auto|].
  econstructor; eauto.
Qed.

Theorem refines_refl:
  forall (step: Step Msg) sys, step # step |-- sys ⊑[id] sys.
Proof.
  unfold Refines; intros.
  rewrite map_id.
  assumption.
Qed.

Theorem refines_trans:
  forall (step1 step2 step3: Step Msg) s1 s2 s3 p q,
    step1 # step2 |-- s1 ⊑[p] s2 ->
    step2 # step3 |-- s2 ⊑[q] s3 ->
    step1 # step3 |-- s1 ⊑[fun l => q (p l)] s3.
Proof.
  unfold Refines; intros.
  specialize (H0 _ (H _ H1)).
  replace (map _ ll) with (map q (map p ll)); [assumption|].
  clear; induction ll; simpl; auto.
  f_equal; auto.
Qed.
  
