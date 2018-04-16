Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepT.

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

  Lemma firstMP_InMP:
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

  Lemma FirstMP_InMP:
    forall (msg: MsgT) mp,
      FirstMP mp msg ->
      InMP msg mp.
  Proof.
    unfold FirstMP; intros.
    eapply firstMP_InMP; eauto.
  Qed.

  Lemma ForallMP_InMP_SubList:
    forall (msgs: list MsgT) mp,
      ForallMP (fun msg => InMP msg mp) msgs ->
      SubList msgs mp.
  Proof.
    induction msgs; intros; [apply SubList_nil|].
    inv H0.
    apply SubList_cons; auto.
  Qed.

  Lemma ForallMP_forall:
    forall P mp,
      ForallMP P mp <->
      (forall msg: MsgT, InMP msg mp -> P msg).
  Proof.
    intros; apply Forall_forall.
  Qed.

  Lemma ForallMP_SubList:
    forall P (mp1 mp2: MessagePool MsgT),
      ForallMP P mp2 ->
      SubList mp1 mp2 ->
      ForallMP P mp1.
  Proof.
    intros.
    apply ForallMP_forall; intros.
    eapply ForallMP_forall in H0; eauto.
    apply H1; auto.
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

  Lemma ForallMP_removeMP:
    forall (P: MsgT -> Prop) msg mp,
      ForallMP P mp ->
      ForallMP P (removeMP msg mp).
  Proof.
    induction mp; simpl; intros; auto.
    inv H0.
    cbn; destruct (msgAddr_dec _ _); auto.
    constructor; auto.
    apply ForallMP_deqMP; auto.
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

  Lemma ForallMP_removeMsgs:
    forall (P: MsgT -> Prop) (dmsgs: list MsgT) mp,
      ForallMP P mp ->
      ForallMP P (removeMsgs dmsgs mp).
  Proof.
    induction dmsgs; simpl; intros; auto.
    apply IHdmsgs.
    apply ForallMP_removeMP; auto.
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

  Lemma findMP_MsgAddr:
    forall from to chn msg mp,
      hd_error (findMP from to chn mp) = Some msg ->
      mid_addr (msg_id (getMsg msg)) = buildMsgAddr from to chn.
  Proof.
    induction mp; simpl; intros; [discriminate|].
    destruct (msgAddr_dec _ _); auto.
    inv H0; auto.
  Qed.

  Lemma firstMP_MsgAddr:
    forall from to chn mp msg,
      firstMP from to chn mp = Some msg ->
      mid_addr (msg_id (getMsg msg)) = buildMsgAddr from to chn.
  Proof.
    unfold firstMP; intros.
    eapply findMP_MsgAddr; eauto.
  Qed.

  Lemma removeMP_deqMP:
    forall msg mid mp,
      msg_id (getMsg msg) = mid ->
      removeMP msg mp = deqMP (mid_from mid) (mid_to mid) (mid_chn mid) mp.
  Proof.
    intros; subst; reflexivity.
  Qed.

  Lemma firstMP_FirstMP:
    forall from to chn mp msg,
      firstMP from to chn mp = Some msg ->
      FirstMP mp msg.
  Proof.
    unfold FirstMP; intros.
    pose proof (firstMP_MsgAddr _ _ _ _ H0).
    destruct (msg_id (getMsg msg)) as [[ ]]; cbn in *.
    inv H1; assumption.
  Qed.

End MessagePoolFacts.

Section MessagePoolMap.
  Variables (MsgT1 MsgT2: Type).
  Context `{HasMsg MsgT1} `{HasMsg MsgT2}.

  Variable (mmap: MsgT1 -> MsgT2).
  Hypothesis (Hmmap: forall msg, getMsg (mmap msg) = getMsg msg).

  Lemma mmap_findMP:
    forall from to chn mp,
      findMP from to chn (map mmap mp) =
      map mmap (findMP from to chn mp).
  Proof.
    induction mp; simpl; intros; auto.
    rewrite IHmp.
    rewrite Hmmap.
    destruct (msgAddr_dec _ _); auto.
  Qed.

  Lemma mmap_firstMP:
    forall from to chn mp,
      firstMP from to chn (map mmap mp) =
      lift mmap (firstMP from to chn mp).
  Proof.
    unfold firstMP; intros.
    rewrite mmap_findMP.
    apply eq_sym, lift_hd_error.
  Qed.

  Lemma mmap_FirstMP:
    forall mp msg,
      FirstMP mp msg ->
      FirstMP (map mmap mp) (mmap msg).
  Proof.
    unfold FirstMP; intros.
    rewrite mmap_firstMP.
    rewrite Hmmap.
    rewrite H1.
    reflexivity.
  Qed.

  Lemma mmap_deqMP:
    forall mp from to chn,
      map mmap (deqMP from to chn mp) =
      deqMP from to chn (map mmap mp).
  Proof.
    induction mp; simpl; intros; auto.
    rewrite Hmmap.
    destruct (msgAddr_dec _ _); auto.
    simpl; rewrite IHmp; auto.
  Qed.
    
  Lemma mmap_removeMP:
    forall mp msg,
      map mmap (removeMP msg mp) =
      removeMP (mmap msg) (map mmap mp).
  Proof.
    unfold removeMP; intros.
    rewrite Hmmap.
    apply mmap_deqMP.
  Qed.

  Lemma mmap_distributeMsgs:
    forall mp msgs,
      map mmap (distributeMsgs msgs mp) =
      distributeMsgs (map mmap msgs) (map mmap mp).
  Proof.
    unfold distributeMsgs; intros.
    apply map_app.
  Qed.
    
End MessagePoolMap.

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
  clear -H3 H7.
  induction ins; [constructor|].
  inv H7.
  constructor; auto.
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
  destruct H9.
  clear -H H0.
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

