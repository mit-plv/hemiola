Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepT StepM.

Require Import Omega.

Set Implicit Arguments.

Lemma addRules_indices:
  forall rules sys,
    indicesOf (addRules rules sys) = indicesOf sys.
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

Corollary addRules_isExternal:
  forall rules sys,
    isExternal (addRules rules sys) =
    isExternal sys.
Proof.
  unfold isExternal; intros.
  rewrite addRules_indices.
  reflexivity.
Qed.
  
Corollary addRules_isInternal:
  forall rules sys,
    isInternal (addRules rules sys) =
    isInternal sys.
Proof.
  unfold isInternal; intros.
  rewrite addRules_indices.
  reflexivity.
Qed.

Corollary addRules_behaviorOf:
  forall sys rules hst,
    behaviorOf (addRules rules sys) hst = behaviorOf sys hst.
Proof.
  induction hst; [reflexivity|].
  simpl; rewrite IHhst; reflexivity.
Qed.

Lemma buildRawSys_indicesOf:
  forall {SysT} `{IsSystem SysT} `{HasInit SysT OStates} (sys: SysT),
    indicesOf sys = indicesOf (buildRawSys sys).
Proof.
  intros; unfold indicesOf, buildRawSys; simpl.
  reflexivity.
Qed.

Corollary buildRawSys_isExternal:
  forall {SysT} `{IsSystem SysT} `{HasInit SysT OStates} (sys: SysT),
    isExternal (buildRawSys sys) = isExternal sys.
Proof.
  unfold isExternal; intros.
  rewrite <-buildRawSys_indicesOf.
  reflexivity.
Qed.

Corollary buildRawSys_isInternal:
  forall {SysT} `{IsSystem SysT} `{HasInit SysT OStates} (sys: SysT),
    isInternal (buildRawSys sys) = isInternal sys.
Proof.
  unfold isInternal; intros.
  rewrite <-buildRawSys_indicesOf.
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
    rulesOf (addRules rules (buildRawSys sys)) = rules.
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

Section System.
  Variable sys: System.

  Lemma internal_external_negb:
    forall idx,
      isInternal sys idx = negb (isExternal sys idx).
  Proof.
    unfold isInternal, isExternal; intros.
    find_if_inside; auto.
  Qed.
  
  Lemma internal_not_external:
    forall idx,
      isInternal sys idx = true -> isExternal sys idx = false.
  Proof.
    unfold isInternal, isExternal; intros.
    find_if_inside; auto.
  Qed.

  Lemma external_not_internal:
    forall idx,
      isExternal sys idx = true -> isInternal sys idx = false.
  Proof.
    unfold isInternal, isExternal; intros.
    find_if_inside; auto.
  Qed.

  Lemma internal_external_false:
    forall idx,
      isInternal sys idx = true -> isExternal sys idx = true -> False.
  Proof.
    unfold isInternal, isExternal; intros.
    find_if_inside; intuition.
  Qed.

  Context {MsgT: Type} `{HasMsg MsgT}.

  Lemma fromInternal_fromExternal_negb:
    forall msg: MsgT,
      fromInternal sys msg = negb (fromExternal sys msg).
  Proof.
    unfold fromInternal, fromExternal; intros.
    apply internal_external_negb.
  Qed.
  
  Lemma fromInternal_not_fromExternal:
    forall msg: MsgT,
      fromInternal sys msg = true -> fromExternal sys msg = false.
  Proof.
    unfold fromInternal, fromExternal; intros.
    apply internal_not_external; auto.
  Qed.

  Lemma fromExternal_not_fromInternal:
    forall msg: MsgT,
      fromExternal sys msg = true -> fromInternal sys msg = false.
  Proof.
    unfold fromInternal, fromExternal; intros.
    apply external_not_internal; auto.
  Qed.

  Lemma fromInternal_fromExternal_false:
    forall msg: MsgT,
      fromInternal sys msg = true -> fromExternal sys msg = true -> False.
  Proof.
    unfold fromInternal, fromExternal; intros.
    eapply internal_external_false; eauto.
  Qed.

  Lemma toInternal_toExternal_negb:
    forall msg: MsgT,
      toInternal sys msg = negb (toExternal sys msg).
  Proof.
    unfold toInternal, toExternal; intros.
    apply internal_external_negb.
  Qed.
  
  Lemma toInternal_not_toExternal:
    forall msg: MsgT,
      toInternal sys msg = true -> toExternal sys msg = false.
  Proof.
    unfold toInternal, toExternal; intros.
    apply internal_not_external; auto.
  Qed.

  Lemma toExternal_not_toInternal:
    forall msg: MsgT,
      toExternal sys msg = true -> toInternal sys msg = false.
  Proof.
    unfold toInternal, toExternal; intros.
    apply external_not_internal; auto.
  Qed.

  Lemma toInternal_toExternal_false:
    forall msg: MsgT,
      toInternal sys msg = true -> toExternal sys msg = true -> False.
  Proof.
    unfold toInternal, toExternal; intros.
    eapply internal_external_false; eauto.
  Qed.

  Lemma internal_extOuts_nil:
    forall (mouts: list MsgT),
      Forall (fun tmsg => toInternal sys tmsg = true) mouts ->
      extOuts sys (map getMsg mouts) = nil.
  Proof.
    induction mouts; simpl; intros; [reflexivity|].
    inv H0; unfold id, toExternal in *.
    rewrite internal_not_external by assumption; auto.
  Qed.

  Lemma intOuts_Forall:
    forall (msgs: list MsgT),
      Forall (fun msg => toInternal sys msg = true) msgs ->
      intOuts sys msgs = msgs.
  Proof.
    induction msgs; simpl; intros; [reflexivity|].
    inv H0; rewrite H3.
    rewrite IHmsgs by assumption.
    reflexivity.
  Qed.

End System.

Lemma extOuts_same_indicesOf:
  forall (sys1 sys2: System) {MsgT} `{HasMsg MsgT} (msgs: list MsgT),
    indicesOf sys1 = indicesOf sys2 ->
    extOuts sys1 msgs = extOuts sys2 msgs.
Proof.
  unfold extOuts, toExternal, isExternal; intros.
  rewrite H0; reflexivity.
Qed.

Lemma intOuts_same_indicesOf:
  forall (sys1 sys2: System) {MsgT} `{HasMsg MsgT} (msgs: list MsgT),
    indicesOf sys1 = indicesOf sys2 ->
    intOuts sys1 msgs = intOuts sys2 msgs.
Proof.
  unfold intOuts, toInternal, isInternal; intros.
  rewrite H0; reflexivity.
Qed.

Lemma ValidMsgsIn_getMsg_eq_part_1:
  forall {MsgT1} `{HasMsg MsgT1} oidx (mins1: list MsgT1),
    Forall
      (fun msg: MsgT1 => mid_to (msg_id (getMsg msg)) = oidx /\
                         mid_from (msg_id (getMsg msg)) <> oidx) mins1 ->
    forall {MsgT2} `{HasMsg MsgT2} (mins2: list MsgT2),
      map getMsg mins1 = map getMsg mins2 ->
      Forall
        (fun msg: MsgT2 =>
           mid_to (msg_id (getMsg msg)) = oidx /\
           mid_from (msg_id (getMsg msg)) <> oidx) mins2.
Proof.
  induction mins1; simpl; intros.
  - apply eq_sym, map_eq_nil in H2; subst.
    constructor.
  - destruct mins2 as [|b mins2]; [discriminate|].
    simpl in H2; inv H2.
    inv H0.
    constructor; auto.
    rewrite <-H4; auto.
Qed.

Lemma ValidMsgsIn_getMsg_eq_part_2:
  forall {MsgT1} `{HasMsg MsgT1} (mins1: list MsgT1),
    NoDup (map (fun m: MsgT1 => (mid_from (msg_id (getMsg m)),
                                 mid_chn (msg_id (getMsg m)))) mins1) ->
    forall {MsgT2} `{HasMsg MsgT2} (mins2: list MsgT2),
      map getMsg mins1 = map getMsg mins2 ->
      NoDup (map (fun m: MsgT2 => (mid_from (msg_id (getMsg m)),
                                   mid_chn (msg_id (getMsg m)))) mins2).
Proof.
  induction mins1; simpl; intros.
  - apply eq_sym, map_eq_nil in H2; subst.
    constructor.
  - destruct mins2 as [|b mins2]; [discriminate|].
    simpl in H2; inv H2.
    inv H0.
    simpl; constructor; auto.

    assert (map (fun m: MsgT1 => (mid_from (msg_id (getMsg m)),
                                  mid_chn (msg_id (getMsg m)))) mins1 =
            map (fun m: MsgT2 => (mid_from (msg_id (getMsg m)),
                                  mid_chn (msg_id (getMsg m)))) mins2).
    { clear -H5.
      generalize dependent mins2.
      induction mins1; simpl; intros.
      { apply eq_sym, map_eq_nil in H5; subst; auto. }
      { destruct mins2 as [|b mins2]; [discriminate|].
        simpl in H5; inv H5.
        simpl.
        erewrite IHmins1 by eassumption.
        rewrite H2; reflexivity.
      }
    }
    
    rewrite <-H4, <-H0; assumption.
Qed.

Lemma ValidMsgsIn_getMsg_eq:
  forall {MsgT1} `{HasMsg MsgT1} oidx (mins1: list MsgT1),
    ValidMsgsIn oidx mins1 ->
    forall {MsgT2} `{HasMsg MsgT2} (mins2: list MsgT2),
      map getMsg mins1 = map getMsg mins2 ->
      ValidMsgsIn oidx mins2.
Proof.
  intros; destruct H0; split.
  - eapply ValidMsgsIn_getMsg_eq_part_1 in H0; [|eassumption].
    assumption.
  - eapply ValidMsgsIn_getMsg_eq_part_2 in H3; [|eassumption].
    assumption.
Qed.

Lemma ValidMsgsIn_MsgAddr_NoDup:
  forall {MsgT} `{HasMsg MsgT} oidx (mins: list MsgT),
    ValidMsgsIn oidx mins ->
    NoDup (map (fun msg => mid_addr (msg_id (getMsg msg))) mins).
Proof.
  intros; destruct H0.
  clear -H1; induction mins; [constructor|].
  inv H1.
  simpl; constructor; auto.
  intro Hx; elim H3; clear -Hx.
  induction mins; [elim Hx|].
  simpl in *; destruct Hx; auto.
  destruct (getMsg a0) as [[[from1 to1 chn1] tid1] val1].
  destruct (getMsg a) as [[[from2 to2 chn2] tid2] val2].
  cbn in *; inv H0.
  auto.
Qed.

Lemma ValidMsgOuts_MsgAddr_NoDup:
  forall {MsgT} `{HasMsg MsgT} oidx (mouts: list MsgT),
    ValidMsgOuts oidx mouts ->
    NoDup (map (fun msg => mid_addr (msg_id (getMsg msg))) mouts).
Proof.
  intros; destruct H0.
  clear -H1; induction mouts; [constructor|].
  inv H1.
  simpl; constructor; auto.
  intro Hx; elim H3; clear -Hx.
  induction mouts; [elim Hx|].
  simpl in *; destruct Hx; auto.
  destruct (getMsg a0) as [[[from1 to1 chn1] tid1] val1].
  destruct (getMsg a) as [[[from2 to2 chn2] tid2] val2].
  cbn in *; inv H0.
  auto.
Qed.

Lemma MsgAddr_NoDup_toTMsg:
  forall (msgs: list Msg),
    NoDup (map (fun msg => mid_addr (msg_id (getMsg msg))) msgs) ->
    forall ti,
      NoDup (map (fun msg => mid_addr (msg_id (getMsg msg))) (toTMsgs ti msgs)).
Proof.
  induction msgs; simpl; intros; [constructor|].
  inv H.
  constructor; auto.
  intro Hx; elim H2; clear -Hx.
  induction msgs; [elim Hx|].
  simpl in *; destruct Hx; auto.
Qed.

Lemma firstMP_ValidMsgId:
  forall from to chn {MsgT} `{HasMsg MsgT} (msg: MsgT) mp,
    firstMP from to chn mp = Some msg ->
    ValidMsgId from to chn msg.
Proof.
  induction mp; unfold firstMP in *; simpl; intros; [discriminate|].
  unfold isAddrOf in H0.
  destruct (msgAddr_dec (mid_addr (msg_id (getMsg a))) (buildMsgAddr from to chn)); auto.
  simpl in H0; inv H0.
  unfold ValidMsgId.
  destruct (getMsg msg) as [mid mv]; destruct mid; simpl in *.
  subst; auto.
Qed.

Lemma idx_in_sys_internal:
  forall oidx {SysT} `{IsSystem SysT} (sys: SysT),
    In oidx (indicesOf sys) ->
    isInternal sys oidx = true.
Proof.
  unfold isInternal; intros.
  find_if_inside; auto.
Qed.

Lemma step_t_int_internal:
  forall sys st1 orule ins outs st2,
    step_t sys st1 (RlblOuts orule ins outs) st2 ->
    Forall (fun msg => toInternal sys msg = true) ins.
Proof.
  intros; inv H; [constructor|].
  clear -H4 H8.
  induction ins; [constructor|].
  assert (ValidMsgsIn (rule_oidx rule) ins)
    by (destruct H8; inv H; inv H0; split; auto).
  constructor; auto.
  destruct H8; inv H0; dest; subst.
  rewrite <-H0 in H4.
  apply idx_in_sys_internal; auto.
Qed.

Lemma step_t_outs_from_internal:
  forall sys st1 ilbl st2,
    step_t sys st1 ilbl st2 ->
    Forall (fun m: TMsg => fromInternal sys m = true)
           (iLblOuts ilbl).
Proof.
  intros; inv H; try (constructor; fail).
  simpl.
  destruct H10.
  clear -H H1.
  induction outs; simpl; intros; [constructor|].
  inv H; dest.
  constructor; auto.
  simpl in H; unfold id in H.
  unfold fromInternal; simpl; rewrite H.
  unfold isInternal; find_if_inside; auto.
Qed.

Lemma extLabel_preserved:
  forall {SysT1 SysT2} `{IsSystem SysT1} `{IsSystem SysT2}
         (impl1: SysT1) (impl2: SysT2),
    indicesOf impl1 = indicesOf impl2 ->
    forall l,
      extLabel impl1 l = extLabel impl2 l.
Proof.
  intros; destruct l; simpl; [reflexivity|].
  unfold extOuts, toExternal, isExternal.
  rewrite H1.
  reflexivity.
Qed.

Lemma step_t_in_rules_weakening:
  forall sys st1 emsg st2,
    step_t sys st1 (RlblIn emsg) st2 ->
    forall wsys,
      indicesOf wsys = indicesOf sys ->
      step_t wsys st1 (RlblIn emsg) st2.
Proof.
  intros; inv H.
  econstructor; auto.
  - unfold fromExternal, isExternal in *; rewrite H0; assumption.
  - unfold toInternal, isInternal in *; rewrite H0; assumption.
Qed.

Lemma step_t_tid_next:
  forall sys st1 orule ins outs ts st2,
    step_t sys st1 (RlblOuts orule ins outs) st2 ->
    outs <> nil ->
    Forall (fun tmsg => tmsg_info tmsg = None) ins ->
    Forall (fun tmsg => match tmsg_info tmsg with
                        | Some ti => tinfo_tid ti = ts
                        | None => True
                        end) outs ->
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
  intros.
  destruct ptst as [poss porqs pmsgs ptid].
  destruct H0 as [? [? ?]]; simpl in *.
  inv H.
  - do 2 eexists; repeat econstructor; eauto.
  - eexists; exists (RlblIn (toTMsgU emsg)).
    split; [|split].
    + econstructor; eauto.
    + reflexivity.
    + repeat split; simpl; auto.
      red in H2; simpl in H2; subst.
      clear; red.
      apply map_app.
  - red in H2; simpl in H2; subst.
    red in H1; simpl in H1.

    assert (exists tmsgs,
               map tmsg_msg tmsgs = msgs /\
               Forall (FirstMP pmsgs) tmsgs).
    { admit. }
    destruct H as [tmsgs [? ?]]; subst.

    eexists.
    eexists (RlblOuts (Some rule) _ _).
    split; [|split].
    + remember (porqs @[rule_oidx rule]) as oorq.
      destruct oorq as [orq|];
        [|specialize (H1 (rule_oidx rule));
          rewrite <-Heqoorq, H6 in H1; exfalso; auto].
      apply eq_sym in Heqoorq.

      econstructor; try reflexivity; try eassumption.
      * auto.
      * eapply ValidMsgsIn_getMsg_eq
          with (mins1:= map tmsg_msg tmsgs); [assumption|].
        clear; induction tmsgs; auto.
        simpl in *.
        rewrite IHtmsgs; reflexivity.
      * rewrite <-H9.
        clear; induction tmsgs; simpl; auto.
        rewrite IHtmsgs; reflexivity.
      * specialize (H1 (rule_oidx rule)).
        rewrite Heqoorq, H6 in H1; subst.
        assumption.
      * instantiate (2:= pos).
        admit.
    + clear.
      cbn; f_equal.
      induction outs; simpl; auto.
      rewrite IHouts; reflexivity.
    + split; [|split]; simpl; auto.
      * admit.
      * red; unfold distributeMsgs.
        rewrite map_app; f_equal.
        { apply mmap_removeMsgs.
          intros; reflexivity.
        }
        { clear; induction outs; simpl; auto.
          destruct (toInternal _ _); auto.
          simpl; rewrite IHouts; reflexivity.
        }
        
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
  destruct (extLabel sys (getLabel a)); simpl; auto.
  f_equal; auto.
Qed.

Lemma behaviorOf_preserved:
  forall {SysT1 SysT2} `{IsSystem SysT1} `{IsSystem SysT2}
         (impl1: SysT1) (impl2: SysT2),
    indicesOf impl1 = indicesOf impl2 ->
    forall hst,
      behaviorOf impl1 hst = behaviorOf impl2 hst.
Proof.
  induction hst; simpl; intros; [reflexivity|].
  rewrite extLabel_preserved with (impl4:= impl2) by assumption.
  rewrite IHhst; reflexivity.
Qed.

Theorem refines_refl:
  forall {SysT StateT LabelT} `{IsSystem SysT} `{HasInit SysT StateT} `{HasLabel LabelT}
         (ss: Steps SysT StateT LabelT) sys, ss # ss |-- sys ⊑[id] sys.
Proof.
  unfold Refines; intros.
  rewrite map_id.
  assumption.
Qed.

Theorem refines_trans:
  forall {SysT StateT LabelT} `{IsSystem SysT} `{HasInit SysT StateT} `{HasLabel LabelT}
         (ss1 ss2 ss3: Steps SysT StateT LabelT) p q s1 s2 s3,
    ss1 # ss2 |-- s1 ⊑[p] s2 ->
    ss2 # ss3 |-- s2 ⊑[q] s3 ->
    ss1 # ss3 |-- s1 ⊑[fun l => q (p l)] s3.
Proof.
  unfold Refines; intros.
  specialize (H3 _ (H2 _ H4)).
  rewrite map_trans in H3.
  assumption.
Qed.

