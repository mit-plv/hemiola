Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepDet.

Require Import Omega.

Set Implicit Arguments.

Section MessagePoolFacts.
  Variable (MsgT: Type).
  Context `{HasMsg MsgT}.

  Lemma firstMP_app_or:
    forall (msg: MsgT) from to chn mp1 mp2,
      firstMP from to chn (mp1 ++ mp2) = Some msg ->
      firstMP from to chn mp1 = Some msg \/
      firstMP from to chn mp2 = Some msg.
  Proof.
    induction mp1; intros; auto.
    unfold firstMP in *; simpl in *.
    destruct (msgAddr_dec _ _).
    - left; inv H0; reflexivity.
    - auto.
  Qed.

  Lemma firstMP_enqMP_or:
    forall (msg nmsg: MsgT) from to chn mp,
      firstMP from to chn (enqMP nmsg mp) = Some msg ->
      msg = nmsg \/ firstMP from to chn mp = Some msg.
  Proof.
    intros.
    apply firstMP_app_or in H0; destruct H0; auto.
    unfold firstMP in H0; cbn in H0.
    destruct (msgAddr_dec _ _); [|discriminate].
    inv H0; auto.
  Qed.

  Lemma firstMP_distributeMsgs_or:
    forall (msg: MsgT) from to chn nmsgs mp,
      firstMP from to chn (distributeMsgs nmsgs mp) = Some msg ->
      firstMP from to chn mp = Some msg \/
      firstMP from to chn nmsgs = Some msg.
  Proof.
    intros.
    apply firstMP_app_or; auto.
  Qed.

  Lemma inMP_enqMP_or:
    forall (msg: MsgT) nmsg mp,
      InMP msg (enqMP nmsg mp) ->
      msg = nmsg \/ InMP msg mp.
  Proof.
    intros.
    apply in_app_or in H0; destruct H0; auto.
    Common.dest_in; auto.
  Qed.

  Lemma inMP_deqMP:
    forall (msg: MsgT) from to chn mp,
      InMP msg (deqMP from to chn mp) ->
      InMP msg mp.
  Proof.
    induction mp; simpl; intros; auto.
    find_if_inside; auto.
    inv H0; auto.
  Qed.

  Lemma inMP_distributeMsgs_or:
    forall (msg: MsgT) nmsgs mp,
      InMP msg (distributeMsgs nmsgs mp) ->
      In msg nmsgs \/ InMP msg mp.
  Proof.
    intros; apply in_app_or in H0; destruct H0; auto.
  Qed.

  Lemma firstMP_inMP:
    forall (msg: MsgT) from to chn mp,
      firstMP from to chn mp = Some msg ->
      InMP msg mp.
  Proof.
    induction mp; simpl; intros; [discriminate|].
    unfold firstMP in H0; simpl in H0.
    destruct (msgAddr_dec _ _).
    - inv H0; auto.
    - right; apply IHmp; auto.
  Qed.

  Lemma ForallMP_forall:
    forall P mp,
      ForallMP P mp <->
      (forall msg: MsgT, InMP msg mp -> P msg).
  Proof.
    intros; apply Forall_forall.
  Qed.

  Lemma ForallMP_enqMP:
    forall (P: MsgT -> Prop) (msg: MsgT) mp,
      ForallMP P mp ->
      P msg ->
      ForallMP P (enqMP msg mp).
  Proof.
    intros.
    apply Forall_app; auto.
  Qed.

  Lemma ForallMP_deqMP:
    forall (P: MsgT -> Prop) from to chn mp,
      ForallMP P mp ->
      ForallMP P (deqMP from to chn mp).
  Proof.
    induction mp; simpl; intros; auto.
    inv H0.
    find_if_inside; auto.
    constructor; auto.
    apply IHmp; auto.
  Qed.

  Lemma ForallMP_distributeMsgs:
    forall (P: MsgT -> Prop) (nmsgs: list MsgT) mp,
      ForallMP P mp ->
      ForallMP P nmsgs ->
      ForallMP P (distributeMsgs nmsgs mp).
  Proof.
    intros.
    apply Forall_app; auto.
  Qed.

  Lemma deqMP_SubList:
    forall from to chn mp,
      SubList (deqMP from to chn mp) mp.
  Proof.
    induction mp; simpl; intros; [apply SubList_nil|].
    find_if_inside.
    - right; auto.
    - apply SubList_cons; [left; reflexivity|].
      apply SubList_cons_right; auto.
  Qed.

End MessagePoolFacts.

Lemma ForallMP_removeOnce:
  forall (P: TMsg -> Prop) tmsg mp,
    ForallMP P mp ->
    ForallMP P (removeOnce tmsg_dec tmsg mp).
Proof.
  induction mp; simpl; intros; auto.
  inv H.
  find_if_inside; auto.
  constructor; auto.
  apply IHmp; auto.
Qed.

Lemma obj_in_sys_idx_internal:
  forall obj sys,
    In obj sys ->
    isInternal sys (obj_idx obj) = true.
Proof.
  unfold isInternal; intros.
  find_if_inside; auto.
  elim n.
  apply in_map; auto.
Qed.

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

Lemma internal_extOuts_nil:
  forall sys {MsgT} `{HasMsg MsgT} (mouts: list MsgT),
    Forall
      (fun tmsg => isInternal sys (mid_to (msg_id (getMsg tmsg))) =
                   true) mouts ->
    extOuts sys (map getMsg mouts) = nil.
Proof.
  induction mouts; simpl; intros; [reflexivity|].
  inv H0; unfold id.
  rewrite internal_not_external by assumption; auto.
Qed.

Lemma extOuts_same_indicesOf:
  forall sys1 sys2 {MsgT} `{HasMsg MsgT} (msgs: list MsgT),
    indicesOf sys1 = indicesOf sys2 ->
    extOuts sys1 msgs = extOuts sys2 msgs.
Proof.
  unfold extOuts, isExternal; intros.
  rewrite H0; reflexivity.
Qed.

Lemma intOuts_same_indicesOf:
  forall sys1 sys2 {MsgT} `{HasMsg MsgT} (msgs: list MsgT),
    indicesOf sys1 = indicesOf sys2 ->
    intOuts sys1 msgs = intOuts sys2 msgs.
Proof.
  unfold intOuts, isInternal; intros.
  rewrite H0; reflexivity.
Qed.

Lemma intOuts_Forall:
  forall sys {MsgT} `{HasMsg MsgT} (msgs: list MsgT),
    Forall (fun msg => isInternal sys (mid_to (msg_id (getMsg msg))) = true) msgs ->
    intOuts sys msgs = msgs.
Proof.
  induction msgs; simpl; intros; [reflexivity|].
  inv H0; rewrite H3.
  rewrite IHmsgs by assumption.
  reflexivity.
Qed.

Lemma firstMP_ValidMsgId:
  forall from to chn {MsgT} `{HasMsg MsgT} (msg: MsgT) mp,
    firstMP from to chn mp = Some msg ->
    ValidMsgId from to chn msg.
Proof.
  induction mp; unfold firstMP in *; simpl; intros; [discriminate|].
  destruct (msgAddr_dec (mid_addr (msg_id (getMsg a))) (buildMsgAddr from to chn)); auto.
  simpl in H0; inv H0.
  unfold ValidMsgId.
  destruct (getMsg msg) as [mid mv]; destruct mid; simpl in *.
  subst; auto.
Qed.

Lemma step_det_int_internal:
  forall sys st1 hdl outs st2,
    step_det sys st1 (IlblOuts (Some hdl) outs) st2 ->
    isInternal sys (mid_to (msg_id (getMsg hdl))) = true.
Proof.
  intros; inv H.
  destruct hdl as [fmsg fts]; simpl in *.
  destruct fmsg as [hmid hmv]; simpl in *; subst.
  pose proof (firstMP_ValidMsgId _ _ _ _ H5).
  destruct (rule_mid frule) as [[from to chn] tid].
  inv H; simpl in *.
  unfold isInternal; find_if_inside; auto.
  cbn in n; elim n; apply in_map; assumption.
Qed.

Lemma step_det_outs_from_internal:
  forall sys st1 ilbl st2,
    step_det sys st1 ilbl st2 ->
    Forall (fun m: TMsg => isInternal sys (mid_from (msg_id (getMsg m))) = true)
           (iLblOuts ilbl).
Proof.
  intros; inv H; try (constructor; fail).
  simpl.
  destruct H8.
  clear -H H0.
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

Definition ValidTidState (tst: TState) :=
  ForallMP (fun tmsg =>
              match tmsg_info tmsg with
              | Some ti => tinfo_tid ti <= tst_tid tst
              | None => True
              end) (tst_msgs tst).

Lemma step_det_tid:
  forall st1,
    ValidTidState st1 ->
    forall sys lbl st2,
      step_det sys st1 lbl st2 ->
      ValidTidState st2.
Proof.
  unfold ValidTidState; intros; inv H0; auto.
  - simpl; simpl in H.
    apply ForallMP_enqMP; auto.
    simpl; auto.
  - simpl; simpl in H.
    apply ForallMP_distributeMsgs.
    + apply ForallMP_deqMP.
      clear -H Hts.
      induction oims; simpl; [constructor|].
      inv H; constructor.
      * destruct (tmsg_info a); auto.
        destruct (tmsg_info fmsg); omega.
      * apply IHoims; auto.
    + apply firstMP_inMP in H4.
      eapply ForallMP_forall in H; eauto.
      clear -Hts H.
      apply Forall_filter.
      induction outs; [constructor|].
      constructor; auto.
      simpl; destruct (tmsg_info fmsg); auto.
Qed.

Lemma steps_det_tid:
  forall st1,
    ValidTidState st1 ->
    forall sys hst st2,
      steps_det sys st1 hst st2 ->
      ValidTidState st2.
Proof.
  induction 2; simpl; intros; auto.
  apply step_det_tid in H1; auto.
Qed.

Definition TInfoExists (sys: System) (tst: TState) :=
  ForallMP (fun tmsg =>
              if isInternal sys (mid_from (msg_id (tmsg_msg tmsg)))
              then tmsg_info tmsg <> None
              else tmsg_info tmsg = None) (tst_msgs tst).

Lemma validOuts_from_internal:
  forall sys idx,
    isInternal sys idx = true ->
    forall mouts,
      ValidOuts idx mouts ->
      ForallMP (fun msg => isInternal sys (mid_from (msg_id msg)) = true) mouts.
Proof.
  induction mouts; simpl; intros; [constructor|].
  destruct H0; inv H0; inv H1; dest.
  constructor.
  - simpl in H0; unfold id in H0; rewrite H0; assumption.
  - apply IHmouts; split; auto.
Qed.

Lemma step_det_tinfo:
  forall sys st1,
    TInfoExists sys st1 ->
    forall lbl st2,
      step_det sys st1 lbl st2 ->
      TInfoExists sys st2.
Proof.
  unfold TInfoExists; intros; inv H0; auto.
  - simpl; simpl in H.
    apply ForallMP_enqMP; auto.
    simpl.
    rewrite external_not_internal by assumption; reflexivity.
  - simpl; simpl in H.
    apply ForallMP_distributeMsgs.
    + apply ForallMP_deqMP; auto.
    + pose proof (obj_in_sys_idx_internal _ _ H1).
      eapply validOuts_from_internal in H9; eauto.
      clear -H9; simpl in H9.
      induction outs; [constructor|].
      inv H9.
      simpl; destruct (isInternal sys (mid_to (msg_id a))); auto.
      constructor; cbn.
      * rewrite H1; discriminate.
      * apply IHouts; auto.
Qed.

Lemma steps_det_tinfo:
  forall sys st1,
    TInfoExists sys st1 ->
    forall hst st2,
      steps_det sys st1 hst st2 ->
      TInfoExists sys st2.
Proof.
  induction 2; simpl; intros; auto.
  apply step_det_tinfo in H1; auto.
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

