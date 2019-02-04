Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM.

Require Import Omega.

Set Implicit Arguments.

Open Scope list.

Ltac inv_steps :=
  repeat
    match goal with
    | [H: steps _ _ _ nil _ |- _] => inv H
    | [H: steps _ _ _ (_ :: _) _ |- _] => inv H
    end.

Ltac inv_step :=
  repeat
    match goal with
    | [H: step_m _ _ (RlblInt _ _ _ _) _ |- _] => inv H
    | [H: {| bst_oss := _; bst_orqs := _; bst_msgs := _ |} =
          {| bst_oss := _; bst_orqs := _; bst_msgs := _ |} |- _] => inv H
    end.

Lemma sys_minds_sys_merqs_DisjList:
  forall {oifc} (sys: System oifc), DisjList (sys_minds sys) (sys_merqs sys).
Proof.
  intros.
  eapply DisjList_NoDup; [exact eq_nat_dec|].
  eapply NoDup_app_weakening_1.
  rewrite <-app_assoc.
  apply sys_msg_inds_valid.
Qed.

Lemma sys_merqs_sys_merss_DisjList:
  forall {oifc} (sys: System oifc), DisjList (sys_merqs sys) (sys_merss sys).
Proof.
  intros.
  eapply DisjList_NoDup; [exact eq_nat_dec|].
  eapply NoDup_app_weakening_2.
  apply sys_msg_inds_valid.
Qed.

Lemma sys_minds_sys_merss_DisjList:
  forall {oifc} (sys: System oifc), DisjList (sys_minds sys) (sys_merss sys).
Proof.
  intros.
  eapply DisjList_NoDup; [exact eq_nat_dec|].
  pose proof (sys_msg_inds_valid sys).
  rewrite app_assoc in H.
  apply NoDup_app_comm in H.
  rewrite app_assoc in H.
  apply NoDup_app_weakening_1 in H.
  apply NoDup_app_comm; assumption.
Qed.

Lemma ValidMsgsIn_sys_minds:
  forall {MsgT oifc} `{HasMsg MsgT}
         (sys1: System oifc) (eins: list (Id MsgT)),
    ValidMsgsIn sys1 eins ->
    forall (sys2: System oifc),
      sys_minds sys1 = sys_minds sys2 ->
      sys_merqs sys1 = sys_merqs sys2 ->
      ValidMsgsIn sys2 eins.
Proof.
  unfold ValidMsgsIn; intros.
  dest; split; auto.
  rewrite <-H1, <-H2; assumption.
Qed.

Lemma ValidMsgsOut_sys_minds_sys_merss:
  forall {MsgT oifc} `{HasMsg MsgT} 
         (sys1: System oifc) (eouts: list (Id MsgT)),
    ValidMsgsOut sys1 eouts ->
    forall (sys2: System oifc),
      sys_minds sys1 = sys_minds sys2 ->
      sys_merss sys1 = sys_merss sys2 ->
      ValidMsgsOut sys2 eouts.
Proof.
  unfold ValidMsgsOut; intros.
  dest; split; auto.
  rewrite <-H1, <-H2; assumption.
Qed.

Lemma ValidMsgsExtIn_sys_merqs:
  forall {MsgT oifc} `{HasMsg MsgT} 
         (sys1: System oifc) (eins: list (Id MsgT)),
    ValidMsgsExtIn sys1 eins ->
    forall (sys2: System oifc),
      sys_merqs sys1 = sys_merqs sys2 ->
      ValidMsgsExtIn sys2 eins.
Proof.
  unfold ValidMsgsExtIn; intros.
  dest; split; auto.
  rewrite <-H1; assumption.
Qed.
  
Lemma ValidMsgsExtOut_sys_merss:
  forall {MsgT oifc} `{HasMsg MsgT} 
         (sys1: System oifc) (eouts: list (Id MsgT)),
    ValidMsgsExtOut sys1 eouts ->
    forall (sys2: System oifc),
      sys_merss sys1 = sys_merss sys2 ->
      ValidMsgsExtOut sys2 eouts.
Proof.
  unfold ValidMsgsExtOut; intros.
  dest; split; auto.
  rewrite <-H1; assumption.
Qed.

Lemma extRssOf_In_sys_merss_FirstMP:
  forall {oifc} (sys: System oifc) msgs1 msgs2,
    extRssOf sys msgs1 = extRssOf sys msgs2 ->
    forall mout,
      In (idOf mout) (sys_merss sys) ->
      FirstMP msgs1 (idOf mout) (valOf mout) ->
      FirstMP msgs2 (idOf mout) (valOf mout).
Proof.
  unfold extRssOf; intros.
  eapply qsOf_In_FirstMP; eauto.
Qed.

Corollary extRssOf_SubList_sys_merss_FirstMP:
  forall {oifc} (sys: System oifc) msgs1 msgs2,
    extRssOf sys msgs1 = extRssOf sys msgs2 ->
    forall mouts,
      SubList (idsOf mouts) (sys_merss sys) ->
      Forall (FirstMPI msgs1) mouts ->
      Forall (FirstMPI msgs2) mouts.
Proof.
  induction mouts; simpl; intros; [constructor|].
  apply SubList_cons_inv in H0; dest.
  inv H1; constructor; auto.
  unfold FirstMPI in *.
  eauto using extRssOf_In_sys_merss_FirstMP.
Qed.

Corollary extRssOf_ValidMsgsExtOut_sys_merss_FirstMP:
  forall {oifc} (sys: System oifc) msgs1 msgs2,
    extRssOf sys msgs1 = extRssOf sys msgs2 ->
    forall mouts,
      ValidMsgsExtOut sys mouts ->
      Forall (FirstMPI msgs1) mouts ->
      Forall (FirstMPI msgs2) mouts.
Proof.
  intros.
  destruct H0.
  eauto using extRssOf_SubList_sys_merss_FirstMP.
Qed.

Lemma init_IntMsgsEmpty:
  forall {oifc} (sys: System oifc), IntMsgsEmpty sys (emptyMP Msg).
Proof.
  intros; red; intros.
  reflexivity.
Qed.

Lemma steps_singleton:
  forall {oifc} (sys: System oifc) st1 lbl st2,
    step_m sys st1 lbl st2 ->
    steps step_m sys st1 [lbl] st2.
Proof.
  intros.
  repeat econstructor.
  assumption.
Qed.

Lemma steps_wfHistory:
  forall {oifc} (sys: System oifc) st1 hst st2,
    steps step_m sys st1 hst st2 ->
    WfHistory sys hst.
Proof.
  induction 1; simpl; intros; [constructor|].
  constructor; auto.
  clear H; inv H0; red; auto 7.
  do 2 eexists; eauto 9.
Qed.

Lemma steps_split:
  forall {SystemT StateT LabelT} 
         (step: Step SystemT StateT LabelT) sys st1 st2 ll,
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
  forall {SystemT StateT LabelT} 
         (step: Step SystemT StateT LabelT) sys st1 ll1 st2,
    steps step sys st1 ll1 st2 ->
    forall ll2 st3,
      steps step sys st2 ll2 st3 ->
      steps step sys st1 (ll2 ++ ll1) st3.
Proof.
  induction 2; simpl; intros; [auto|].
  econstructor; eauto.
Qed.

Lemma reachable_init:
  forall {SystemT StateT LabelT} `{HasInit SystemT StateT} `{HasLabel LabelT}
         (step: Step SystemT StateT LabelT) sys,
    Reachable (steps step) sys (initsOf sys).
Proof.
  eexists; econstructor.
Qed.

Lemma reachable_steps:
  forall {SystemT StateT LabelT} `{HasInit SystemT StateT} `{HasLabel LabelT}
         (step: Step SystemT StateT LabelT) sys st1,
    Reachable (steps step) sys st1 ->
    forall ll st2,
      steps step sys st1 ll st2 ->
      Reachable (steps step) sys st2.
Proof.
  unfold Reachable; intros; dest.
  eexists; eapply steps_append; eauto.
Qed.
  
Lemma behaviorOf_app:
  forall {LabelT} `{HasLabel LabelT} (hst1 hst2: list LabelT),
    behaviorOf (hst1 ++ hst2) =
    behaviorOf hst1 ++ behaviorOf hst2.
Proof.
  induction hst1; simpl; intros; auto.
  rewrite IHhst1.
  destruct (getLabel a); reflexivity.
Qed.

Theorem refines_refl:
  forall {SystemT StateT LabelT} `{HasInit SystemT StateT} `{HasLabel LabelT}
         (ss: Steps SystemT StateT LabelT) sys, ss # ss |-- sys ⊑ sys.
Proof.
  unfold Refines; intros.
  assumption.
Qed.

Theorem refines_trans:
  forall {SystemT StateT LabelT} `{HasInit SystemT StateT} `{HasLabel LabelT}
         (ss1 ss2 ss3: Steps SystemT StateT LabelT) s1 s2 s3,
    ss1 # ss2 |-- s1 ⊑ s2 ->
    ss2 # ss3 |-- s2 ⊑ s3 ->
    ss1 # ss3 |-- s1 ⊑ s3.
Proof.
  unfold Refines; intros.
  specialize (H2 _ (H1 _ H3)).
  assumption.
Qed.

Close Scope list.

