Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepT StepM.

Require Import Omega.

Set Implicit Arguments.

Lemma addRules_indices:
  forall rules sys,
    oindsOf (addRules rules sys) = oindsOf sys.
Proof.
  reflexivity.
Qed.

Lemma addRules_OStates_inits:
  forall rules sys,
    initsOf (StateT:= OStates) (addRules rules sys) = initsOf sys.
Proof.
  reflexivity.
Qed.

Lemma addRules_TState_inits:
  forall rules sys,
    initsOf (StateT:= TState) (addRules rules sys) = initsOf sys.
Proof.
  reflexivity.
Qed.

Corollary addRules_behaviorOf:
  forall sys rules hst,
    behaviorOf (addRules rules sys) hst = behaviorOf sys hst.
Proof.
  induction hst; [reflexivity|].
  simpl; rewrite IHhst; reflexivity.
Qed.

Lemma buildRawSys_oindsOf:
  forall {SysT} `{IsSystem SysT} `{HasInit SysT OStates} (sys: SysT),
    oindsOf sys = oindsOf (buildRawSys sys).
Proof.
  intros; unfold oindsOf, buildRawSys; simpl.
  reflexivity.
Qed.

Lemma addRules_app:
  forall sys rules1 rules2,
    addRules (rules1 ++ rules2) sys =
    addRules rules2 (addRules rules1 sys).
Proof.
  unfold addRules; simpl; intros.
  rewrite app_assoc; reflexivity.
Qed.

Lemma addRulesSys_buildRawSys:
  forall rules sys,
    sys_rules (addRules rules (buildRawSys sys)) = rules.
Proof.
  reflexivity.
Qed.

Lemma getTMsgsTInfo_Some:
  forall tmsgs ti,
    getTMsgsTInfo tmsgs = Some ti ->
    exists tmsg,
      In tmsg tmsgs /\ tmsg_info tmsg = Some ti.
Proof.
  induction tmsgs; simpl; intros; [discriminate|].
  destruct a as [amsg ati]; simpl in *.
  destruct ati.
  - inv H; eexists; intuition idtac.
  - specialize (IHtmsgs _ H); destruct IHtmsgs as [tmsg [? ?]].
    exists tmsg; intuition idtac.
Qed.

Lemma getTMsgsTInfo_Forall_Some:
  forall tmsgs ti,
    tmsgs <> nil ->
    Forall (fun tmsg => tmsg_info tmsg = Some ti) tmsgs ->
    getTMsgsTInfo tmsgs = Some ti.
Proof.
  induction tmsgs; simpl; intros; [elim H; reflexivity|].
  inv H0; rewrite H3; reflexivity.
Qed.

Lemma getTMsgsTInfo_Forall_None:
  forall tmsgs,
    Forall (fun tmsg => tmsg_info tmsg = None) tmsgs ->
    getTMsgsTInfo tmsgs = None.
Proof.
  induction tmsgs; simpl; intros; [reflexivity|].
  inv H; rewrite H2; auto.
Qed.

Lemma ValidMsgsIn_mindsOf:
  forall {MsgT SysT} `{HasMsg MsgT} `{IsSystem SysT}
         (sys1: SysT) (eins: list (Id MsgT)),
    ValidMsgsIn sys1 eins ->
    forall sys2,
      mindsOf sys1 = mindsOf sys2 ->
      ValidMsgsIn sys2 eins.
Proof.
  unfold ValidMsgsIn; intros.
  dest; split; auto.
  rewrite <-H2; assumption.
Qed.

Lemma ValidMsgsExtIn_merqsOf:
  forall {MsgT SysT} `{HasMsg MsgT} `{IsSystem SysT}
         (sys1: SysT) (eins: list (Id MsgT)),
    ValidMsgsExtIn sys1 eins ->
    forall sys2,
      merqsOf sys1 = merqsOf sys2 ->
      ValidMsgsExtIn sys2 eins.
Proof.
  unfold ValidMsgsExtIn; intros.
  dest; split; auto.
  rewrite <-H2; assumption.
Qed.
  
Lemma ValidMsgsExtOut_merssOf:
  forall {MsgT SysT} `{HasMsg MsgT} `{IsSystem SysT}
         (sys1: SysT) (eouts: list (Id MsgT)),
    ValidMsgsExtOut sys1 eouts ->
    forall sys2,
      merssOf sys1 = merssOf sys2 ->
      ValidMsgsExtOut sys2 eouts.
Proof.
  unfold ValidMsgsExtOut; intros.
  dest; split; auto.
  rewrite <-H2; assumption.
Qed.

Lemma step_t_tid_next:
  forall sys st1 orule ins outs ts st2,
    step_t sys st1 (RlblInt orule ins outs) st2 ->
    outs <> nil ->
    Forall (fun tmsg => tmsg_info tmsg = None) (valsOf ins) ->
    Forall (fun tmsg => match tmsg_info tmsg with
                        | Some ti => tinfo_tid ti = ts
                        | None => True
                        end) (valsOf outs) ->
    tst_tid st2 = ts.
Proof.
  intros.
  inv H.
  - elim H0; reflexivity.
  - simpl.
    apply getTMsgsTInfo_Forall_None in H1.
    rewrite H1 in *.
    clear -H0 H2.
    destruct outs0 as [|out ?].
    + elim H0; reflexivity.
    + inv H2; simpl in H3; auto.
Qed.

Lemma extRssOf_In_merssOf_FirstMP:
  forall {SysT} `{IsSystem SysT} (sys: SysT) msgs1 msgs2,
    extRssOf sys msgs1 = extRssOf sys msgs2 ->
    forall mout,
      In (idOf mout) (merssOf sys) ->
      FirstMP msgs1 (idOf mout) (valOf mout) ->
      FirstMP msgs2 (idOf mout) (valOf mout).
Proof.
  give_up.
Admitted.

Corollary extRssOf_SubList_merssOf_FirstMP:
  forall {SysT} `{IsSystem SysT} (sys: SysT) msgs1 msgs2,
    extRssOf sys msgs1 = extRssOf sys msgs2 ->
    forall mouts,
      SubList (idsOf mouts) (merssOf sys) ->
      Forall (FirstMPI msgs1) mouts ->
      Forall (FirstMPI msgs2) mouts.
Proof.
  induction mouts; simpl; intros; [constructor|].
  apply SubList_cons_inv in H1; dest.
  inv H2; constructor; auto.
  unfold FirstMPI in *.
  eauto using extRssOf_In_merssOf_FirstMP.
Qed.

Corollary extRssOf_ValidMsgsExtOut_merssOf_FirstMP:
  forall {SysT} `{IsSystem SysT} (sys: SysT) msgs1 msgs2,
    extRssOf sys msgs1 = extRssOf sys msgs2 ->
    forall mouts,
      ValidMsgsExtOut sys mouts ->
      Forall (FirstMPI msgs1) mouts ->
      Forall (FirstMPI msgs2) mouts.
Proof.
  intros.
  destruct H1.
  eauto using extRssOf_SubList_merssOf_FirstMP.
Qed.
  
Theorem step_t_sound:
  forall sys pst lbl nst,
    step_m sys pst lbl nst ->
    forall ptst,
      TStateRel ptst pst ->
      exists ntst tlbl,
        step_t sys ptst tlbl ntst /\
        tToMLabel tlbl = lbl /\
        TStateRel ntst nst.
Proof.
  admit.
Admitted.

Lemma steps_split:
  forall {SysT StateT LabelT} `{IsSystem SysT}
         (step: Step SysT StateT LabelT) sys st1 st2 ll,
    steps step sys st1 ll st2 ->
    forall ll1 ll2,
      ll = ll2 ++ ll1 ->
      exists sti,
        steps step sys st1 ll1 sti /\
        steps step sys sti ll2 st2.
Proof.
  induction 2; simpl; intros.
  - apply eq_sym, app_eq_nil in H0; dest; subst.
    eexists; split; econstructor.
  - destruct ll2.
    + simpl in H2; subst.
      specialize (IHsteps ll nil eq_refl).
      destruct IHsteps as [tsi [? ?]].
      inv H3.
      eexists; split.
      * econstructor; eauto.
      * econstructor.
    + simpl in H2; inv H2.
      specialize (IHsteps _ _ eq_refl).
      destruct IHsteps as [sti [? ?]].
      eexists; split; eauto.
      econstructor; eauto.
Qed.

Lemma steps_append:
  forall {SysT StateT LabelT} `{IsSystem SysT}
         (step: Step SysT StateT LabelT) sys st1 ll1 st2,
    steps step sys st1 ll1 st2 ->
    forall ll2 st3,
      steps step sys st2 ll2 st3 ->
      steps step sys st1 (ll2 ++ ll1) st3.
Proof.
  induction 3; simpl; intros; [auto|].
  econstructor; eauto.
Qed.

Lemma behaviorOf_app:
  forall (sys: System)
         {LabelT} `{HasLabel LabelT} (hst1 hst2: list LabelT),
    behaviorOf sys (hst1 ++ hst2) =
    behaviorOf sys hst1 ++ behaviorOf sys hst2.
Proof.
  induction hst1; simpl; intros; auto.
  rewrite IHhst1.
  destruct (getLabel a); reflexivity.
Qed.

Lemma behaviorOf_preserved:
  forall {SysT1 SysT2} `{IsSystem SysT1} `{IsSystem SysT2}
         (impl1: SysT1) (impl2: SysT2),
    oindsOf impl1 = oindsOf impl2 ->
    forall hst,
      behaviorOf impl1 hst = behaviorOf impl2 hst.
Proof.
  induction hst; simpl; intros; [reflexivity|].
  rewrite IHhst; reflexivity.
Qed.

Theorem refines_refl:
  forall {SysT StateT LabelT} `{IsSystem SysT} `{HasInit SysT StateT} `{HasLabel LabelT}
         (ss: Steps SysT StateT LabelT) sys, ss # ss |-- sys ⊑ sys.
Proof.
  unfold Refines; intros.
  assumption.
Qed.

Theorem refines_trans:
  forall {SysT StateT LabelT} `{IsSystem SysT} `{HasInit SysT StateT} `{HasLabel LabelT}
         (ss1 ss2 ss3: Steps SysT StateT LabelT) s1 s2 s3,
    ss1 # ss2 |-- s1 ⊑ s2 ->
    ss2 # ss3 |-- s2 ⊑ s3 ->
    ss1 # ss3 |-- s1 ⊑ s3.
Proof.
  unfold Refines; intros.
  specialize (H3 _ (H2 _ H4)).
  assumption.
Qed.

