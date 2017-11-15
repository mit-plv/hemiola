Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Wf Semantics SemFacts StepDet StepSeq.
Require Import Serial SerialFacts Simulation Predicate Synthesis.

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
    getStateInit (addPMsgsSys pmsgs sys) = getStateInit sys.
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

Theorem simulation_pmsgs_compositional:
  forall {StateS LabelS: Type} `{HasInit StateS} `{HasLabel LabelS}
         (stepS: Step StateS LabelS)
         impl1 impl2 spec simR simP
         (Hidx: indicesOf impl1 = indicesOf impl2)
         (Hsim1: Simulates step_det stepS simR simP impl1 spec)
         (Hsim2: Simulates step_det stepS simR simP impl2 spec)
         impl (Hii: indicesOf impl = indicesOf impl1)
         (Himplp:
            forall pmsg iobj,
              In pmsg (obj_trs iobj) ->
              In iobj (sys_objs impl) ->
              exists obj,
                obj_idx obj = obj_idx iobj /\
                In pmsg (obj_trs obj) /\
                In obj (sys_objs impl1 ++ sys_objs impl2)),
    Simulates step_det stepS simR simP impl spec.
Proof.
  unfold Simulates; intros.
  specialize (Hsim1 ist1 sst1 H1 ilbl ist2).
  specialize (Hsim2 ist1 sst1 H1 ilbl ist2).

  destruct ilbl as [|[hdl|]];
    [apply Hsim1; eapply step_det_in_pmsgs_weakening; eauto|
     |inv H2; apply Hsim1; constructor].
  
  match goal with
  | [ |- ?g ] =>
    assert (Hsp: step_det impl1 ist1 (IlblOuts (Some hdl) mouts) ist2 \/
                 step_det impl2 ist1 (IlblOuts (Some hdl) mouts) ist2 -> g)
      by (intro Hsp; destruct Hsp; [apply Hsim1; assumption|apply Hsim2; assumption])
  end.
  apply Hsp; clear Hsp Hsim1 Hsim2.
  inv H2.

  - specialize (Himplp _ _ H13 H5); destruct Himplp as [iobj [? [? ?]]].
    apply in_app_or in H4; destruct H4.
    + left.
      replace (extOuts impl) with (extOuts impl1)
        by (unfold extOuts, isExternal; rewrite Hii; reflexivity).
      replace (intOuts impl) with (intOuts impl1)
        by (unfold intOuts, isInternal; rewrite Hii; reflexivity).
      eapply SdIntFwd; eauto.
      unfold isInternal; rewrite <-Hii; assumption.
    + right.
      replace (extOuts impl) with (extOuts impl2)
        by (unfold extOuts, isExternal; rewrite Hii, Hidx; reflexivity).
      replace (intOuts impl) with (intOuts impl2)
        by (unfold intOuts, isInternal; rewrite Hii, Hidx; reflexivity).
      eapply SdIntFwd; eauto.
      unfold isInternal; rewrite <-Hidx, <-Hii; assumption.

  - specialize (Himplp _ _ H13 H5); destruct Himplp as [iobj [? [? ?]]].
    apply in_app_or in H4; destruct H4.
    + left.
      replace (extOuts impl) with (extOuts impl1)
        by (unfold extOuts, isExternal; rewrite Hii; reflexivity).
      replace (intOuts impl) with (intOuts impl1)
        by (unfold intOuts, isInternal; rewrite Hii; reflexivity).
      eapply SdIntInit; eauto.
      unfold isInternal; rewrite <-Hii; assumption.
    + right.
      replace (extOuts impl) with (extOuts impl2)
        by (unfold extOuts, isExternal; rewrite Hii, Hidx; reflexivity).
      replace (intOuts impl) with (intOuts impl2)
        by (unfold intOuts, isInternal; rewrite Hii, Hidx; reflexivity).
      eapply SdIntInit; eauto.
      unfold isInternal; rewrite <-Hidx, <-Hii; assumption.
Qed.

Lemma buildRawSys_indicesOf:
  forall sys, indicesOf sys = indicesOf (buildRawSys sys).
Proof.
  intros; destruct sys as [obs chns].
  unfold indicesOf, buildRawSys; simpl.
  clear chns; induction obs; [reflexivity|].
  simpl; rewrite IHobs; reflexivity.
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

Corollary simulation_pmsgs_added:
  forall {StateS LabelS: Type} `{HasInit StateS} `{HasLabel LabelS}
         (stepS: Step StateS LabelS)
         impl pmsgs spec simR simP
         (Hsim1: Simulates step_det stepS simR simP impl spec)
         (Hsim2: Simulates step_det stepS simR simP
                           (addPMsgsSys pmsgs (buildRawSys impl)) spec),
    Simulates step_det stepS simR simP (addPMsgsSys pmsgs impl) spec.
Proof.
  intros.
  eapply simulation_pmsgs_compositional
    with (impl1:= impl) (impl2:= addPMsgsSys pmsgs (buildRawSys impl)); eauto.
  - rewrite addPMsgsSys_indices.
    apply buildRawSys_indicesOf.
  - apply addPMsgsSys_indices.
  - clear; intros.
    apply addPMsgsSys_pmsg_in; auto.
Qed.

