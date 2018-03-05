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

Fact SdIntSingle:
  forall sys ts nts (Hts: nts > ts) tinfo
         oss oims oidx os pos fmsg frule fidx fchn outs,
    In oidx (indicesOf sys) ->
    (oss)@[oidx] = Some os ->
    
    firstMP fidx oidx fchn oims = Some fmsg -> 
    
    msg_id (getMsg fmsg) :: nil = rule_mids frule ->
    In frule (sys_rules sys) ->
    rule_precond frule os (tmsg_msg fmsg :: nil) ->
    rule_postcond frule os (tmsg_msg fmsg :: nil) pos outs ->
    ValidMsgOuts oidx outs ->
    
    tinfo = match tmsg_info fmsg with
            | Some finfo => finfo
            | None => {| tinfo_tid := nts;
                         tinfo_rqin := tmsg_msg fmsg :: nil |}
            end ->
    
    step_det sys
             {| tst_oss := oss;
                tst_msgs := oims;
                tst_tid := ts
             |}
             (RlblOuts (Some frule) (fmsg :: nil) (toTMsgs tinfo outs))
             {| tst_oss := oss +[ oidx <- pos ];
                tst_msgs := distributeMsgs
                              (intOuts sys (toTMsgs tinfo outs))
                              (deqMP fidx oidx fchn oims);
                tst_tid := match tmsg_info fmsg with
                           | Some _ => ts
                           | None => nts
                           end
             |}.
Proof.
  intros.
  replace (tmsg_info fmsg) with (getTMsgsTInfo (fmsg :: nil))
    by (simpl; destruct (tmsg_info fmsg); reflexivity).
  replace (deqMP fidx oidx fchn oims) with (removeMsgs (fmsg :: nil) oims)
    by (cbn; erewrite removeMP_deqMP by reflexivity;
        apply firstMP_MsgAddr in H1;
        destruct (msg_id (getMsg fmsg)) as [[ ]]; subst; simpl in *;
        inv H1; cbn; reflexivity).
  change (msg_value (tmsg_msg fmsg) :: nil) with
      (map (fun tmsg => msg_value (tmsg_msg tmsg)) (fmsg :: nil)).
  eapply SdInt; eauto.
  - repeat constructor.
    eapply firstMP_FirstMP; eauto.
  - repeat constructor.
    apply firstMP_MsgAddr in H1.
    simpl; simpl in H1; destruct (msg_id (tmsg_msg fmsg)) as [[ ]].
    inv H1; reflexivity.
  - simpl; subst.
    destruct (tmsg_info fmsg); reflexivity.
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

  Lemma internal_extOuts_nil:
    forall {MsgT} `{HasMsg MsgT} (mouts: list MsgT),
      Forall (fun tmsg => isInternal sys (mid_to (msg_id (getMsg tmsg))) =
                          true) mouts ->
      extOuts sys (map getMsg mouts) = nil.
  Proof.
    induction mouts; simpl; intros; [reflexivity|].
    inv H0; unfold id.
    rewrite internal_not_external by assumption; auto.
  Qed.

  Lemma intOuts_Forall:
    forall {MsgT} `{HasMsg MsgT} (msgs: list MsgT),
      Forall (fun msg => isInternal sys (mid_to (msg_id (getMsg msg))) = true) msgs ->
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
  unfold extOuts, isExternal; intros.
  rewrite H0; reflexivity.
Qed.

Lemma intOuts_same_indicesOf:
  forall (sys1 sys2: System) {MsgT} `{HasMsg MsgT} (msgs: list MsgT),
    indicesOf sys1 = indicesOf sys2 ->
    intOuts sys1 msgs = intOuts sys2 msgs.
Proof.
  unfold intOuts, isInternal; intros.
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
  forall oidx {SysT StateT} `{IsSystem SysT StateT} (sys: SysT),
    In oidx (indicesOf sys) ->
    isInternal sys oidx = true.
Proof.
  unfold isInternal; intros.
  find_if_inside; auto.
Qed.

Lemma step_det_int_internal:
  forall sys st1 orule ins outs st2,
    step_det sys st1 (RlblOuts orule ins outs) st2 ->
    Forall (fun msg => isInternal sys (mid_to (msg_id (getMsg msg))) = true) ins.
Proof.
  intros; inv H; [constructor|].
  clear -H3 H6.
  induction ins; [constructor|].
  inv H6.
  constructor; auto.
  apply idx_in_sys_internal; auto.  
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
Qed.

Lemma extLabel_preserved:
  forall (impl1 impl2: System),
    indicesOf impl1 = indicesOf impl2 ->
    forall l,
      extLabel impl1 l = extLabel impl2 l.
Proof.
  intros; destruct l; simpl; [reflexivity|].
  unfold extOuts, isExternal.
  rewrite H.
  reflexivity.
Qed.

Lemma step_det_in_rules_weakening:
  forall sys st1 emsg st2,
    step_det sys st1 (RlblIn emsg) st2 ->
    forall wsys,
      indicesOf wsys = indicesOf sys ->
      step_det wsys st1 (RlblIn emsg) st2.
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
    + apply ForallMP_removeMsgs.
      clear -H Hts.
      induction oims; simpl; [constructor|].
      inv H; constructor.
      * destruct (tmsg_info a); auto.
        destruct (getTMsgsTInfo msgs); omega.
      * apply IHoims; auto.
    + apply Forall_impl with (Q:= fun msg => InMP msg oims) in H3;
        [|intros; eapply FirstMP_InMP; eauto].
      apply ForallMP_InMP_SubList in H3.
      eapply ForallMP_SubList in H3; eauto.

      clear -Hts H3.
      apply Forall_filter.
      induction outs; [constructor|].
      constructor; auto.

      simpl; remember (getTMsgsTInfo msgs) as ti; destruct ti; auto.
      apply eq_sym, getTMsgsTInfo_Some in Heqti.
      destruct Heqti as [tmsg [? ?]].
      eapply ForallMP_forall in H3; eauto.
      rewrite H0 in H3; auto.
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

Lemma validMsgOuts_from_internal:
  forall sys idx,
    isInternal sys idx = true ->
    forall mouts,
      ValidMsgOuts idx mouts ->
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
    + apply ForallMP_removeMsgs; auto.
    + pose proof (idx_in_sys_internal _ _ H1).
      eapply validMsgOuts_from_internal in H9; eauto.
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
  forall {SysT StateT LabelT} `{IsSystem SysT StateT}
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
  forall {SysT StateT LabelT} `{IsSystem SysT StateT}
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
  forall (impl1 impl2: System),
    indicesOf impl1 = indicesOf impl2 ->
    forall hst,
      behaviorOf impl1 hst = behaviorOf impl2 hst.
Proof.
  induction hst; simpl; intros; [reflexivity|].
  rewrite extLabel_preserved with (impl2:= impl2) by assumption.
  rewrite IHhst; reflexivity.
Qed.

Theorem refines_refl:
  forall {SysT StateT LabelT} `{IsSystem SysT StateT} `{HasLabel LabelT}
         (ss: Steps SysT StateT LabelT) sys, ss # ss |-- sys ⊑[id] sys.
Proof.
  unfold Refines; intros.
  rewrite map_id.
  assumption.
Qed.

Theorem refines_trans:
  forall {SysT StateT LabelT} `{IsSystem SysT StateT} `{HasLabel LabelT}
         (ss1 ss2 ss3: Steps SysT StateT LabelT) p q s1 s2 s3,
    ss1 # ss2 |-- s1 ⊑[p] s2 ->
    ss2 # ss3 |-- s2 ⊑[q] s3 ->
    ss1 # ss3 |-- s1 ⊑[fun l => q (p l)] s3.
Proof.
  unfold Refines; intros.
  specialize (H2 _ (H1 _ H3)).
  rewrite map_trans in H2.
  assumption.
Qed.

