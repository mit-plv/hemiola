Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics SemFacts StepDet StepSeq.
Require Import Serial SerialFacts Simulation Predicate Synthesis.

Lemma addPMsg_nil:
  forall pmsg,
    addPMsg pmsg nil = nil.
Proof.
  reflexivity.
Qed.

Lemma addPMsgs_nil:
  forall pmsgs,
    addPMsgs pmsgs nil = nil.
Proof.
  induction pmsgs; simpl; intros; auto.
Qed.

Lemma addPMsg_init:
  forall pmsg objs,
    getObjectStatesInit (addPMsg pmsg objs) =
    getObjectStatesInit objs.
Proof.
  induction objs; simpl; intros; [reflexivity|].
  find_if_inside; simpl; auto.
  rewrite IHobjs.
  reflexivity.
Qed.

Lemma addPMsgs_init:
  forall pmsgs objs,
    getObjectStatesInit (addPMsgs pmsgs objs) =
    getObjectStatesInit objs.
Proof.
  induction pmsgs; simpl; intros; [reflexivity|].
  rewrite IHpmsgs.
  apply addPMsg_init.
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

Lemma addPMsg_indices:
  forall pmsg objs,
    map (fun o => obj_idx o) (addPMsg pmsg objs) =
    map (fun o => obj_idx o) objs.
Proof.
  induction objs; simpl; intros; [reflexivity|].
  find_if_inside; simpl; auto.
  rewrite IHobjs; reflexivity.
Qed.

Lemma addPMsgs_indices:
  forall pmsgs objs,
    map (fun o => obj_idx o) (addPMsgs pmsgs objs) =
    map (fun o => obj_idx o) objs.
Proof.
  induction pmsgs; simpl; intros; [reflexivity|].
  rewrite IHpmsgs.
  apply addPMsg_indices.
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
         (Hii: iisOf impl1 = iisOf impl2)
         (Hsim1: Simulates step_det stepS simR simP impl1 spec)
         (Hsim2: Simulates step_det stepS simR simP impl2 spec)
         impl (Himplii: iisOf impl = iisOf impl1)
         (Himplp: SubList (pmsgsOf impl) (pmsgsOf impl1 ++ pmsgsOf impl2)),
    Simulates step_det stepS simR simP impl spec.
Proof.
  unfold Simulates; intros.
  specialize (Hsim1 ist1 sst1 H1 ilbl ist2).
  specialize (Hsim2 ist1 sst1 H1 ilbl ist2).

  destruct ilbl.
  - apply Hsim1.
    eapply step_det_in_pmsgs_weakening; eauto.
    apply iisOf_indicesOf; auto.
  - destruct mhdl as [hdl|];
      [|inv H2; apply Hsim1; constructor].

    pose proof (step_det_pmsgs_in _ _ _ _ H2) as Hhdl.
    simpl in Hhdl; destruct Hhdl as [hpmsg [? ?]].
    specialize (Himplp _ H3).
    apply in_app_or in Himplp.
    destruct Himplp.

    + apply Hsim1.
      admit.
    + apply Hsim2.
      admit.
    
Admitted.

