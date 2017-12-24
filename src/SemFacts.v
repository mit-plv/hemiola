Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepDet.

Lemma internal_external_negb:
  forall sys idx,
    isInternal sys idx = negb (isExternal sys idx).
Proof.
  unfold isInternal, isExternal; intros.
  find_if_inside; auto.
Qed.
  
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
    step_det sys st1 (IlblOuts (Some hdl) outs) st2 ->
    isInternal sys (mid_to (msg_id (getMsg hdl))) = true.
Proof.
  intros; inv H.
  destruct fmsg as [fmsg fts]; simpl in *.
  destruct fmsg as [hmid hmv]; simpl in *; subst.
  destruct H6 as [? [? ?]]; simpl in *; subst.
  rewrite H0.
  unfold isInternal; find_if_inside; auto.
  elim n; apply in_map; assumption.
Qed.

Lemma step_det_outs_from_internal:
  forall sys st1 ilbl st2,
    step_det sys st1 ilbl st2 ->
    Forall (fun m: TMsg => isInternal sys (mid_from (msg_id (getMsg m))) = true)
           (iLblOuts ilbl).
Proof.
  intros; inv H; try (constructor; fail).
  simpl.
  destruct H11.
  clear -H H0.
  remember (rule_outs _ _ _) as outs; clear Heqouts.
  induction outs; simpl; intros; [constructor|].
  inv H; dest.
  constructor; auto.
  simpl; simpl in H; unfold id in H; rewrite H.
  unfold isInternal; find_if_inside; auto.
  elim n; apply in_map; assumption.
Qed.

Lemma extLabel_preserved:
  forall impl1 impl2,
    indicesOf impl1 = indicesOf impl2 ->
    forall l,
      extLabel impl1 l = extLabel impl2 l.
Proof.
  intros; destruct l; simpl; [reflexivity|].
  unfold extOuts, isExternal.
  rewrite H.
  reflexivity.
Qed.

Lemma step_det_silent_rules_weakening:
  forall sys st1 mouts st2,
    step_det sys st1 (IlblOuts None mouts) st2 ->
    forall wsys,
      indicesOf wsys = indicesOf sys ->
      step_det wsys st1 (IlblOuts None mouts) st2.
Proof.
  intros; inv H.
  constructor.
Qed.

Lemma step_det_in_rules_weakening:
  forall sys st1 emsg st2,
    step_det sys st1 (IlblIn emsg) st2 ->
    forall wsys,
      indicesOf wsys = indicesOf sys ->
      step_det wsys st1 (IlblIn emsg) st2.
Proof.
  intros; inv H.
  constructor; auto.
  - unfold isExternal in *; rewrite H0; assumption.
  - unfold isInternal in *; rewrite H0; assumption.
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

Lemma steps_det_silent:
  forall sys hst1 hst2 st1 st2,
    steps_det sys st1 (hst1 ++ emptyILabel :: hst2) st2 ->
    steps_det sys st1 (hst1 ++ hst2) st2.
Proof.
  intros.
  eapply steps_split in H; [|reflexivity]; destruct H as [sti [? ?]].
  inv H; inv H6.
  eapply steps_append; eauto.
Qed.

Lemma behaviorOf_app:
  forall {LabelT} `{HasLabel LabelT} sys (hst1 hst2: list LabelT),
    behaviorOf sys (hst1 ++ hst2) =
    behaviorOf sys hst1 ++ behaviorOf sys hst2.
Proof.
  induction hst1; simpl; intros; auto.
  destruct (extLabel sys (getLabel a)); simpl; auto.
  f_equal; auto.
Qed.

Lemma behaviorOf_preserved:
  forall impl1 impl2,
    indicesOf impl1 = indicesOf impl2 ->
    forall hst,
      behaviorOf impl1 hst = behaviorOf impl2 hst.
Proof.
  induction hst; simpl; intros; [reflexivity|].
  rewrite extLabel_preserved with (impl2:= impl2) by assumption.
  rewrite IHhst; reflexivity.
Qed.

Theorem refines_refl:
  forall {StateT LabelT} `{HasInit StateT} `{HasLabel LabelT}
         (ss: Steps StateT LabelT) sys, ss # ss |-- sys ⊑[id] sys.
Proof.
  unfold Refines; intros.
  rewrite map_id.
  assumption.
Qed.

Theorem refines_trans:
  forall {StateT LabelT} `{HasInit StateT} `{HasLabel LabelT}
         (ss1 ss2 ss3: Steps StateT LabelT) p q s1 s2 s3,
    ss1 # ss2 |-- s1 ⊑[p] s2 ->
    ss2 # ss3 |-- s2 ⊑[q] s3 ->
    ss1 # ss3 |-- s1 ⊑[fun l => q (p l)] s3.
Proof.
  unfold Refines; intros.
  specialize (H2 _ (H1 _ H3)).
  rewrite map_trans in H2.
  assumption.
Qed.

