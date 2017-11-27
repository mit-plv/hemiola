Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Wf Semantics SemFacts StepDet StepSeq.
Require Import Serial SerialFacts Simulation Predicate Synthesis.

Lemma simEquiv_refl:
  forall os, SimEquiv os os.
Proof.
  unfold SimEquiv; intros.
  mred.
  constructor; intros; auto.
Qed.

Lemma simEquiv_OState_eq_1:
  forall oss1 oss2,
    SimEquiv oss1 oss2 ->
    forall oidx ost1,
      oss1@[oidx] = Some ost1 -> ost_tst ost1 = [] ->
      exists ost2,
        oss2@[oidx] = Some ost2 /\ ost_st ost2 = ost_st ost1.
Proof.
  intros.
  specialize (H oidx).
  rewrite H0 in H.
  destruct (oss2@[oidx]); [|exfalso; auto].
  specialize (H (or_introl H1)).
  destruct o, ost1; simpl in *; subst.
  eexists; eauto.
Qed.

Lemma simEquiv_OState_eq_2:
  forall oss1 oss2,
    SimEquiv oss1 oss2 ->
    forall oidx ost2,
      oss2@[oidx] = Some ost2 -> ost_tst ost2 = [] ->
      exists ost1,
        oss1@[oidx] = Some ost1 /\ ost_st ost1 = ost_st ost2.
Proof.
  intros.
  specialize (H oidx).
  rewrite H0 in H.
  destruct (oss1@[oidx]); [|exfalso; auto].
  specialize (H (or_intror H1)).
  destruct o, ost2; simpl in *; subst.
  eexists; eauto.
Qed.

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

Theorem simulation_pmsgs_compositional:
  forall {StateS LabelS: Type} `{HasInit StateS} `{HasLabel LabelS}
         (stepS: Step StateS LabelS)
         impl1 impl2 spec simR simP
         (Hidx: indicesOf impl1 = indicesOf impl2)
         (Hsim1: Simulates step_seq stepS simR simP impl1 spec)
         (Hsim2: Simulates step_seq stepS simR simP impl2 spec)
         impl (Hii: indicesOf impl = indicesOf impl1)
         (Himplp:
            forall pmsg iobj,
              In pmsg (obj_trs iobj) ->
              In iobj (sys_objs impl) ->
              exists obj,
                obj_idx obj = obj_idx iobj /\
                In pmsg (obj_trs obj) /\
                In obj (sys_objs impl1 ++ sys_objs impl2)),
    Simulates step_seq stepS simR simP impl spec.
Proof.
  unfold Simulates; intros.
  specialize (Hsim1 ist1 sst1 H1 ilbl ist2).
  specialize (Hsim2 ist1 sst1 H1 ilbl ist2).

  destruct ilbl as [|[hdl|]];
    [apply Hsim1; eapply step_seq_in_pmsgs_weakening; eauto|
     |inv H2; apply Hsim1; constructor].
  
  match goal with
  | [ |- ?g ] =>
    assert (Hsp: step_seq impl1 ist1 (IlblOuts (Some hdl) mouts) ist2 \/
                 step_seq impl2 ist1 (IlblOuts (Some hdl) mouts) ist2 -> g)
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
      eapply SsIntInit; eauto.
      unfold isExternal in *; rewrite <-Hii; assumption.
    + right.
      replace (extOuts impl) with (extOuts impl2)
        by (unfold extOuts, isExternal; rewrite Hii, Hidx; reflexivity).
      replace (intOuts impl) with (intOuts impl2)
        by (unfold intOuts, isInternal; rewrite Hii, Hidx; reflexivity).
      eapply SsIntInit; eauto.
      unfold isExternal in *; rewrite <-Hidx, <-Hii; assumption.

  - specialize (Himplp _ _ H13 H5); destruct Himplp as [iobj [? [? ?]]].
    apply in_app_or in H4; destruct H4.
    + left.
      replace (extOuts impl) with (extOuts impl1)
        by (unfold extOuts, isExternal; rewrite Hii; reflexivity).
      replace (intOuts impl) with (intOuts impl1)
        by (unfold intOuts, isInternal; rewrite Hii; reflexivity).
      eapply SsIntFwd; eauto.
      unfold isInternal; rewrite <-Hii; assumption.
    + right.
      replace (extOuts impl) with (extOuts impl2)
        by (unfold extOuts, isExternal; rewrite Hii, Hidx; reflexivity).
      replace (intOuts impl) with (intOuts impl2)
        by (unfold intOuts, isInternal; rewrite Hii, Hidx; reflexivity).
      eapply SsIntFwd; eauto.
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
         (Hsim1: Simulates step_seq stepS simR simP impl spec)
         (Hsim2: Simulates step_seq stepS simR simP
                           (addPMsgsSys pmsgs (buildRawSys impl)) spec),
    Simulates step_seq stepS simR simP (addPMsgsSys pmsgs impl) spec.
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
  
Lemma simTrs_preserved_lock_added:
  forall R oss oims ts sst,
    SimTrs R {| tst_oss := oss; tst_msgs := oims; tst_tid := ts |} sst ->
    forall noidx pos,
      oss@[noidx] = Some pos ->
      forall nos ntrsIdx ntrs,
        nos = {| ost_st := ost_st pos;
                 ost_tst := (ost_tst pos) +[ntrsIdx <- ntrs]
              |} ->
        forall nmsgs nts,
          SimTrs R {| tst_oss := oss +[noidx <- nos];
                      tst_msgs := nmsgs;
                      tst_tid := nts |} sst.
Proof.
  intros; subst.
  inv H; econstructor; eauto.
  simpl in *.
  unfold SimEquiv in *; intros.
  specialize (H1 oidx).
  findeq.
  - unfold SimEquivO in *; simpl; intros.
    rewrite H0 in H1.
    destruct H.
    + exfalso; eapply M.add_empty_neq; eauto.
    + apply H1; auto.
  - rewrite H0 in H1; auto.
Qed.

