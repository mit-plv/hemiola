Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Wf Semantics SemFacts StepDet Synthesis.
Require Import Serial SerialFacts Simulation TrsInv TrsSim.

Lemma addRules_init:
  forall rules objs,
    getObjectStatesInit (addRules rules objs) =
    getObjectStatesInit objs.
Proof.
  induction objs; simpl; intros; [reflexivity|].
  rewrite IHobjs.
  reflexivity.
Qed.

Lemma addRulesSys_init:
  forall rules sys,
    getStateInit (StateT:= TState) (addRulesSys rules sys) =
    getStateInit (StateT:= TState) sys.
Proof.
  unfold addRulesSys; simpl; intros.
  unfold getTStateInit; simpl.
  rewrite addRules_init.
  reflexivity.
Qed.

Lemma addRules_indices:
  forall rules objs,
    map (fun o => obj_idx o) (addRules rules objs) =
    map (fun o => obj_idx o) objs.
Proof.
  induction objs; simpl; intros; [reflexivity|].
  rewrite IHobjs.
  reflexivity.
Qed.

Lemma addRulesSys_indices:
  forall rules sys,
    indicesOf (addRulesSys rules sys) = indicesOf sys.
Proof.
  unfold addRulesSys; simpl; intros.
  unfold indicesOf; simpl.
  apply addRules_indices.
Qed.

Corollary addRulesSys_isExternal:
  forall rules sys,
    isExternal (addRulesSys rules sys) =
    isExternal sys.
Proof.
  unfold isExternal; intros.
  rewrite addRulesSys_indices.
  reflexivity.
Qed.
  
Corollary addRulesSys_isInternal:
  forall rules sys,
    isInternal (addRulesSys rules sys) =
    isInternal sys.
Proof.
  unfold isInternal; intros.
  rewrite addRulesSys_indices.
  reflexivity.
Qed.

Lemma buildRawSys_indicesOf:
  forall sys, indicesOf sys = indicesOf (buildRawSys sys).
Proof.
  intros; unfold indicesOf, buildRawSys; simpl.
  induction sys; [reflexivity|].
  simpl; rewrite IHsys; reflexivity.
Qed.

Corollary buildRawSys_isExternal:
  forall sys,
    isExternal (buildRawSys sys) =
    isExternal sys.
Proof.
  unfold isExternal; intros.
  rewrite <-buildRawSys_indicesOf.
  reflexivity.
Qed.

Corollary buildRawSys_isInternal:
  forall sys,
    isInternal (buildRawSys sys) =
    isInternal sys.
Proof.
  unfold isInternal; intros.
  rewrite <-buildRawSys_indicesOf.
  reflexivity.
Qed.

Lemma addRules_rule_in:
  forall rule rules obs iobj,
    In rule (obj_rules iobj) ->
    In iobj (addRules rules obs) ->
    exists obj : Object,
      obj_idx obj = obj_idx iobj /\
      In rule (obj_rules obj) /\
      In obj (obs ++ addRules rules (buildRawObjs obs)).
Proof.
  induction obs; simpl; intros; [intuition idtac|].
  destruct H0; subst.
  - clear IHobs.
    unfold addRulesO in H; simpl in H.
    apply in_app_or in H; destruct H.
    + exists (addRulesO rules
                        {| obj_idx := obj_idx a;
                           obj_state_init := obj_state_init a;
                           obj_rules := nil |}); simpl; repeat split.
      * rewrite app_nil_r; assumption.
      * right; apply in_or_app; right.
        left; reflexivity.
    + exists a; repeat split; auto.
  - specialize (IHobs _ H H0).
    destruct IHobs as [obj [? [? ?]]].
    exists obj; repeat split; auto.
    right.
    apply in_or_app.
    apply in_app_or in H3; destruct H3.
    + left; assumption.
    + right; right; auto.
Qed.

Lemma addRulesO_app:
  forall obj rules1 rules2,
    addRulesO (rules1 ++ rules2) obj = addRulesO rules1 (addRulesO rules2 obj).
Proof.
  unfold addRulesO; intros; simpl; f_equal.
  rewrite filter_app.
  apply eq_sym, app_assoc.
Qed.
  
Lemma addRules_app:
  forall obs rules1 rules2,
    addRules (rules1 ++ rules2) obs =
    addRules rules1 (addRules rules2 obs).
Proof.
  induction obs; simpl; intros; [reflexivity|].
  rewrite addRulesO_app, IHobs; reflexivity.
Qed.

Lemma addRulesSys_app:
  forall sys rules1 rules2,
    addRulesSys (rules1 ++ rules2) sys =
    addRulesSys rules1 (addRulesSys rules2 sys).
Proof.
  unfold addRulesSys; intros; simpl.
  rewrite addRules_app; reflexivity.
Qed.

Lemma addRulesSys_rule_in:
  forall sys rules rule iobj,
    In rule (obj_rules iobj) ->
    In iobj (addRulesSys rules sys) ->
    exists obj : Object,
      obj_idx obj = obj_idx iobj /\
      In rule (obj_rules obj) /\
      In obj (sys ++ (addRulesSys rules (buildRawSys sys))).
Proof.
  intros; simpl in *.
  apply addRules_rule_in; auto.
Qed.

Lemma addRulesSys_buildRawSys_sublist:
  forall rules sys,
    SubList (rulesOf (addRulesSys rules (buildRawSys sys)))
            rules.
Proof.
  unfold rulesOf; intros; simpl.
  induction sys; [simpl; apply SubList_nil|].

  simpl.
  apply SubList_app_3; [|assumption].
  apply SubList_app_3; [|apply SubList_nil].
  clear; induction rules; [apply SubList_nil|].
  simpl; find_if_inside.
  - apply SubList_cons; [left; reflexivity|].
    apply SubList_cons_right; assumption.
  - apply SubList_cons_right; assumption.
Qed.

Lemma rollbacked_enqMP_toTMsgU:
  forall (mp: Msg -> Msg) msgs emsg rb,
    enqMP (toTMsgU (mp emsg)) (deinitialize mp (rollbacked rb msgs)) =
    deinitialize mp (rollbacked rb (enqMP (toTMsgU emsg) msgs)).
Proof.
  induction msgs; simpl; intros.
  - unfold deinitialize, enqMP.
    rewrite map_app; simpl.
    reflexivity.
  - destruct (tmsg_info a); eauto.
Qed.

Lemma SimMP_ext_msg_in:
  forall (mp: Msg -> Msg) imsgs smsgs,
    SimMP mp imsgs smsgs ->
    forall emsg,
      SimMP mp (enqMP (toTMsgU emsg) imsgs)
            (enqMP (toTMsgU (mp emsg)) smsgs).
Proof.
  unfold SimMP; intros; subst.
  unfold rollback.
  apply rollbacked_enqMP_toTMsgU.
Qed.

Lemma rollbacked_app:
  forall mp1 rb mp2,
    rollbacked rb (mp1 ++ mp2) =
    rollbacked (rollbacked rb mp1) mp2.
Proof.
  induction mp1; simpl; intros; [reflexivity|].
  destruct (tmsg_info a); auto.
Qed.

Lemma deinitialize_addActive_diff_msgs:
  forall mp msg1 msg2 tinfo rb,
    deinitialize mp (addActive msg1 tinfo rb) =
    deinitialize mp (addActive msg2 tinfo rb).
Proof.
  induction rb; simpl; intros; [reflexivity|].
  destruct (tmsg_info a); auto.
  find_if_inside; auto.
  find_if_inside; auto.
  simpl; rewrite IHrb; reflexivity.
Qed.

Lemma SimMP_int_msg_begin:
  forall (mp: Msg -> Msg) imsgs smsgs,
    SimMP mp imsgs smsgs ->
    forall from to chn rqin,
      firstMP from to chn imsgs = Some {| tmsg_msg := rqin; tmsg_info := None |} ->
      forall tid,
        ForallMP (fun tmsg =>
                    match tmsg_info tmsg with
                    | Some ti => tinfo_tid ti < tid
                    | None => True
                    end) imsgs ->
        forall mouts,
          mouts <> nil ->
          Forall (fun tmsg => tmsg_info tmsg = Some {| tinfo_tid := tid; tinfo_rqin := rqin |}) mouts ->
          SimMP mp (distributeMsgs mouts (deqMP from to chn imsgs)) smsgs.
Proof.
Admitted.

Lemma SimMP_int_msg_fwd:
  forall (mp: Msg -> Msg) imsgs smsgs,
    SimMP mp imsgs smsgs ->
    forall from to chn imsg ti,
      firstMP from to chn imsgs = Some {| tmsg_msg := imsg; tmsg_info := Some ti |} ->
      forall mouts,
        mouts <> nil ->
        Forall (fun tmsg => tmsg_info tmsg = Some ti) mouts ->
        SimMP mp (distributeMsgs mouts (deqMP from to chn imsgs)) smsgs.
Proof.
Admitted.

Corollary trsSimulates_trsInvHolds_rules_added:
  forall impl rules spec simR ginv simP
         (Hsim1: TrsSimulates simR ginv simP impl spec)
         (Hinv1: TrsInv impl ginv)
         (Hmt1: trsPreservingSys impl)
         (Hsim2: TrsSimulates simR ginv simP (addRulesSys rules (buildRawSys impl)) spec)
         (Hinv1: TrsInv (addRulesSys rules (buildRawSys impl)) ginv)
         (Hmt2: trsPreservingSys (addRulesSys rules (buildRawSys impl)))
         (Hmtdisj: TrsDisj (rulesOf impl) rules),
    TrsSimulates simR ginv simP (addRulesSys rules impl) spec /\
    TrsInv (addRulesSys rules impl) ginv.
Proof.
  intros.
  eapply trsSimulates_trsInvHolds_compositional
    with (impl1:= impl) (impl2:= addRulesSys rules (buildRawSys impl)); eauto.
  - rewrite addRulesSys_indices.
    apply buildRawSys_indicesOf.
  - unfold TrsDisjSys.
    eapply TrsDisj_SubList_2; eauto.
    apply addRulesSys_buildRawSys_sublist.
  - admit. (* should be easily derivable from [Hmt1] and [Hmt2] *)
  - apply addRulesSys_indices.
  - apply addRulesSys_rule_in; auto.
Admitted.

