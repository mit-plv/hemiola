Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Wf Semantics SemFacts StepDet.
Require Import Serial SerialFacts Simulation TrsSim Predicate Synthesis.

Lemma addPMsgs_init:
  forall pmsgs objs,
    getObjectStatesInit (addPMsgs pmsgs objs) =
    getObjectStatesInit objs.
Proof.
  induction objs; simpl; intros; [reflexivity|].
  rewrite IHobjs.
  reflexivity.
Qed.

Lemma addPMsgsSys_init:
  forall pmsgs sys,
    getStateInit (StateT:= TState) (addPMsgsSys pmsgs sys) =
    getStateInit (StateT:= TState) sys.
Proof.
  unfold addPMsgsSys; simpl; intros.
  unfold getTStateInit; simpl.
  rewrite addPMsgs_init.
  reflexivity.
Qed.

Lemma addPMsgs_indices:
  forall pmsgs objs,
    map (fun o => obj_idx o) (addPMsgs pmsgs objs) =
    map (fun o => obj_idx o) objs.
Proof.
  induction objs; simpl; intros; [reflexivity|].
  rewrite IHobjs.
  reflexivity.
Qed.

Lemma addPMsgsSys_indices:
  forall pmsgs sys,
    indicesOf (addPMsgsSys pmsgs sys) = indicesOf sys.
Proof.
  unfold addPMsgsSys; simpl; intros.
  unfold indicesOf; simpl.
  apply addPMsgs_indices.
Qed.

Corollary addPMsgsSys_isExternal:
  forall pmsgs sys,
    isExternal (addPMsgsSys pmsgs sys) =
    isExternal sys.
Proof.
  unfold isExternal; intros.
  rewrite addPMsgsSys_indices.
  reflexivity.
Qed.
  
Corollary addPMsgsSys_isInternal:
  forall pmsgs sys,
    isInternal (addPMsgsSys pmsgs sys) =
    isInternal sys.
Proof.
  unfold isInternal; intros.
  rewrite addPMsgsSys_indices.
  reflexivity.
Qed.

Lemma buildRawSys_indicesOf:
  forall sys, indicesOf sys = indicesOf (buildRawSys sys).
Proof.
  intros; destruct sys as [obs chns].
  unfold indicesOf, buildRawSys; simpl.
  clear chns; induction obs; [reflexivity|].
  simpl; rewrite IHobs; reflexivity.
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

Lemma addPMsgs_pmsg_in:
  forall pmsg pmsgs obs iobj,
    In pmsg (obj_trs iobj) ->
    In iobj (addPMsgs pmsgs obs) ->
    exists obj : Object,
      obj_idx obj = obj_idx iobj /\
      In pmsg (obj_trs obj) /\
      In obj (obs ++ addPMsgs pmsgs (buildRawObjs obs)).
Proof.
  induction obs; simpl; intros; [intuition idtac|].
  destruct H0; subst.
  - clear IHobs.
    unfold addPMsgsO in H; simpl in H.
    apply in_app_or in H; destruct H.
    + exists (addPMsgsO pmsgs
                        {| obj_idx := obj_idx a;
                           obj_state_init := obj_state_init a;
                           obj_trs := nil |}); simpl; repeat split.
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

Lemma addPMsgsO_app:
  forall obj pmsgs1 pmsgs2,
    addPMsgsO (pmsgs1 ++ pmsgs2) obj = addPMsgsO pmsgs1 (addPMsgsO pmsgs2 obj).
Proof.
  unfold addPMsgsO; intros; simpl; f_equal.
  rewrite filter_app.
  apply eq_sym, app_assoc.
Qed.
  
Lemma addPMsgs_app:
  forall obs pmsgs1 pmsgs2,
    addPMsgs (pmsgs1 ++ pmsgs2) obs =
    addPMsgs pmsgs1 (addPMsgs pmsgs2 obs).
Proof.
  induction obs; simpl; intros; [reflexivity|].
  rewrite addPMsgsO_app, IHobs; reflexivity.
Qed.

Lemma addPMsgsSys_app:
  forall sys pmsgs1 pmsgs2,
    addPMsgsSys (pmsgs1 ++ pmsgs2) sys =
    addPMsgsSys pmsgs1 (addPMsgsSys pmsgs2 sys).
Proof.
  unfold addPMsgsSys; intros; simpl; f_equal.
  rewrite addPMsgs_app; reflexivity.
Qed.

Lemma addPMsgsSys_pmsg_in:
  forall sys pmsgs pmsg iobj,
    In pmsg (obj_trs iobj) ->
    In iobj (sys_objs (addPMsgsSys pmsgs sys)) ->
    exists obj : Object,
      obj_idx obj = obj_idx iobj /\
      In pmsg (obj_trs obj) /\
      In obj (sys_objs sys ++ sys_objs (addPMsgsSys pmsgs (buildRawSys sys))).
Proof.
  intros; destruct sys as [obs chns]; simpl in *.
  apply addPMsgs_pmsg_in; auto.
Qed.

Lemma addPMsgsSys_buildRawSys_sublist:
  forall pmsgs sys,
    SubList (pmsgsOf (addPMsgsSys pmsgs (buildRawSys sys)))
            pmsgs.
Proof.
  unfold pmsgsOf; intros; simpl.
  induction (sys_objs sys); clear sys;
    [simpl; apply SubList_nil|].

  simpl.
  apply SubList_app_3; [|assumption].
  apply SubList_app_3; [|apply SubList_nil].
  clear; induction pmsgs; [apply SubList_nil|].
  simpl; find_if_inside.
  - apply SubList_cons; [left; reflexivity|].
    apply SubList_cons_right; assumption.
  - apply SubList_cons_right; assumption.
Qed.
  
Corollary trsSimulates_pmsgs_added:
  forall impl pmsgs spec simR simP
         (Hsim1: TrsSimulates simR simP impl spec)
         (Hmt1: mtPreservingSys impl)
         (Hsim2: TrsSimulates simR simP (addPMsgsSys pmsgs (buildRawSys impl)) spec)
         (Hmt2: mtPreservingSys (addPMsgsSys pmsgs (buildRawSys impl)))
         (Hmtdisj: MTypeDisj (pmsgsOf impl) pmsgs),
    TrsSimulates simR simP (addPMsgsSys pmsgs impl) spec.
Proof.
  intros.
  eapply trsSimulates_compositional
    with (impl1:= impl) (impl2:= addPMsgsSys pmsgs (buildRawSys impl)); eauto.
  - rewrite addPMsgsSys_indices.
    apply buildRawSys_indicesOf.
  - unfold MTypeDisjSys.
    eapply MTypeDisj_SubList_2; eauto.
    apply addPMsgsSys_buildRawSys_sublist.
  - admit. (* should be easily derivable from [Hmt1] and [Hmt2] *)
  - apply addPMsgsSys_indices.
  - apply addPMsgsSys_pmsg_in; auto.
Admitted.

