Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap.
Require Import Syntax Semantics SemFacts StepDet Serial.

Require Import Omega.

Set Implicit Arguments.

Lemma SubHistory_refl:
  forall hst, SubHistory hst hst.
Proof.
  intros; exists nil; reflexivity.
Qed.

Lemma SubHistory_cons:
  forall l hst, SubHistory hst (l :: hst).
Proof.
  intros; exists (l :: nil); reflexivity.
Qed.

Lemma SubHistory_In:
  forall l hst1 hst2,
    In l hst1 ->
    SubHistory hst1 hst2 ->
    In l hst2.
Proof.
  unfold SubHistory; intros.
  destruct H0 as [nhsg ?]; subst.
  apply in_or_app; auto.
Qed.

Lemma atomic_emptyILabel_not_in:
  forall sys rqin hst mouts orsout,
    Atomic sys rqin hst mouts orsout ->
    ~ In emptyILabel hst.
Proof.
  induction 1; simpl; intros; [auto| |];
    try (intro Hx; elim IHAtomic; destruct Hx;
         [discriminate|assumption]).
Qed.

Lemma atomic_iLblIn_not_in:
  forall sys rqin hst mouts orsout,
    Atomic sys rqin hst mouts orsout ->
    forall msg,
      ~ In (IlblIn msg) hst.
Proof.
  induction 1; simpl; intros; [auto| |];
    try (intro Hx; destruct Hx;
         [discriminate|firstorder]).
Qed.

Lemma atomic_preserved:
  forall impl1 rqin hst mouts orsout,
    Atomic impl1 rqin hst mouts orsout ->
    forall impl2,
      indicesOf impl1 = indicesOf impl2 ->
      Atomic impl2 rqin hst mouts orsout.
Proof.
  induction 1; simpl; intros.
  - econstructor; eauto.
    unfold isExternal in *.
    rewrite H1 in H; assumption.
  - constructor; auto.
    + unfold isInternal in *.
      rewrite H4 in H1; assumption.
    + unfold isInternal in *.
      rewrite H4 in H2; assumption.
  - constructor; auto.
    + unfold isInternal in *.
      rewrite H2 in H0; assumption.
    + unfold isExternal in *.
      rewrite H2 in H1; assumption.
Qed.

Lemma atomic_rs_out_1:
  forall sys rqin hdl rsout hst mouts orsout,
    Atomic sys rqin (IlblOuts (Some hdl) (rsout :: nil) :: hst) mouts orsout ->
    isExternal sys (mid_to (msg_id (tmsg_msg rsout))) = true ->
    mouts = nil /\ orsout = Some rsout.
Proof.
  intros; inv H.
  - exfalso; inv H10.
    eapply (internal_external_false _ _ H2 H0); eauto.
  - auto.
Qed.

Lemma atomic_rs_out_2:
  forall sys rqin hst mouts rsout,
    Atomic sys rqin hst mouts (Some rsout) ->
    hst <> nil /\
    isExternal sys (mid_to (msg_id (tmsg_msg rsout))) = true /\
    mouts = nil /\
    exists hdl hst', hst = (IlblOuts (Some hdl) (rsout :: nil) :: hst').
Proof.
  intros; inv H.
  repeat split; eauto.
  discriminate.
Qed.

Lemma atomic_mouts_tinfo:
  forall sys rqin hst mouts orsout,
    Atomic sys rqin hst mouts orsout ->
    forall st1 st2,
      steps_det sys st1 hst st2 ->
      ForallMP (fun tmsg => tmsg_info tmsg = Some rqin) mouts.
Proof.
  induction 1; simpl; intros.
  - constructor; auto.
  - inv H4; apply ForallMP_distributeMsgs.
    + eapply ForallMP_deqMP; eauto.
    + inv H10.
      remember (match tmsg_info fmsg with
                | Some finfo => finfo
                | None => {| tinfo_tid := nts; tinfo_rqin := tmsg_msg fmsg |}
                end) as ntinfo; clear Heqntinfo.
      specialize (IHAtomic _ _ H8).
      eapply ForallMP_forall in IHAtomic; eauto.
      simpl in IHAtomic; inv IHAtomic.
      clear; induction (rule_outs _ _ _); [constructor|].
      constructor; auto.
  - constructor.
Qed.

Lemma trsMessages_app:
  forall ti mp1 mp2,
    trsMessages ti (mp1 ++ mp2) =
    trsMessages ti mp1 ++ trsMessages ti mp2.
Proof.
  intros; apply filter_app.
Qed.

Lemma trsMessages_In:
  forall tmsg ti mp,
    In tmsg mp ->
    tmsg_info tmsg = Some ti ->
    In tmsg (trsMessages ti mp).
Proof.
  induction mp; simpl; intros; auto.
  destruct H; subst.
  - rewrite H0.
    destruct (tinfo_dec ti ti); [|elim n; reflexivity].
    left; reflexivity.
  - find_if_inside; auto.
    right; auto.
Qed.

Lemma trsMessages_In_tinfo:
  forall tmsg ti mp,
    In tmsg (trsMessages ti mp) ->
    tmsg_info tmsg = Some ti.
Proof.
  induction mp; simpl; intros; [elim H|].
  remember (tmsg_info a) as oti; destruct oti as [ati|]; auto.
  destruct (tinfo_dec ati ti); subst; auto.
  inv H; auto.
Qed.
  
Lemma trsMessages_SubList:
  forall ti mp1 mp2,
    SubList mp1 mp2 ->
    SubList (trsMessages ti mp1) (trsMessages ti mp2).
Proof.
  induction mp1; simpl; intros; [apply SubList_nil|].
  apply SubList_cons_inv in H; dest.
  remember (tmsg_info a) as tinfo; destruct tinfo; auto.
  destruct (tinfo_dec t ti); subst; auto.
  apply SubList_cons; auto.
  apply trsMessages_In; auto.
Qed.

Lemma trsMessages_deqMP_SubList:
  forall ti from to chn mp,
    SubList (trsMessages ti (deqMP from to chn mp))
            (trsMessages ti mp).
Proof.
  intros.
  apply trsMessages_SubList.
  apply deqMP_SubList.
Qed.

Lemma trsMessages_toTMsg:
  forall ti msgs,
    trsMessages ti (toTMsgs ti msgs) = toTMsgs ti msgs.
Proof.
  induction msgs; simpl; intros; [reflexivity|].
  destruct (tinfo_dec ti ti); [|elim n; reflexivity].
  rewrite IHmsgs; reflexivity.
Qed.

Lemma trsMessages_deqMP_comm:
  forall rqin from to chn mp tmsg,
    firstMP from to chn mp = Some tmsg ->
    tmsg_info tmsg = Some rqin ->
    trsMessages rqin (deqMP from to chn mp) =
    deqMP from to chn (trsMessages rqin mp).
Proof.
  induction mp; simpl; intros; [reflexivity|].
  unfold firstMP in H; simpl in H.
  destruct (msgAddr_dec _ _).
  - inv H; rewrite H0.
    destruct (tinfo_dec _ _); [|elim n; reflexivity].
    simpl; destruct (msgAddr_dec _ _); [|elim n; assumption].
    reflexivity.
  - specialize (IHmp _ H H0).
    simpl; destruct (tmsg_info a); [|assumption].
    destruct (tinfo_dec _ _); subst; [|assumption].
    simpl; destruct (msgAddr_dec _ _); [elim n; assumption|].
    rewrite IHmp; reflexivity.
Qed.

Lemma msgs_tinfo_old':
  forall sys sti ll st,
    steps_det sys sti ll st ->
    sti = getStateInit sys ->
    ForallMP (fun tmsg =>
                match tmsg_info tmsg with
                | Some tinfo => tinfo_tid tinfo <= tst_tid st
                | None => True
                end) (tst_msgs st).
Proof.
  induction 1; simpl; intros; subst.
  - cbn; constructor.
  - specialize (IHsteps eq_refl).
    inv H0; simpl.
    + apply IHsteps; auto.
    + apply ForallMP_enqMP; auto.
      subst; cbn; auto.
    + simpl in IHsteps.
      apply ForallMP_distributeMsgs.
      * destruct (tmsg_info fmsg) as [tinfo|].
        { apply ForallMP_deqMP; auto. }
        { apply ForallMP_deqMP.
          apply ForallMP_forall; intros.
          eapply ForallMP_forall in IHsteps; eauto.
          destruct (tmsg_info msg); [omega|auto].
        }
      * apply firstMP_inMP in H5.
        eapply ForallMP_forall in IHsteps; eauto.
        destruct (tmsg_info fmsg) as [ftinfo|].
        { clear -IHsteps Hts.
          induction (rule_outs _ _ _); [constructor|].
          simpl; find_if_inside; auto.
          constructor; auto.
        }
        { clear.
          induction (rule_outs _ _ _); [constructor|].
          simpl; find_if_inside; auto.
          constructor; auto.
          simpl; omega.
        }
Qed.

Lemma msgs_tinfo_old:
  forall sys st,
    Reachable steps_det sys st ->
    ForallMP (fun tmsg =>
                match tmsg_info tmsg with
                | Some tinfo => tinfo_tid tinfo <= tst_tid st
                | None => True
                end) (tst_msgs st).
Proof.
  intros; inv H.
  eapply msgs_tinfo_old'; eauto.
Qed.

Lemma external_msg_in_tinfo':
  forall sys sti ll st,
    steps_det sys sti ll st ->
    sti = getStateInit sys ->
    forall msgs,
      msgs = tst_msgs st ->
      forall tmsg,
        InMP tmsg msgs ->
        isExternal sys (mid_from (msg_id (tmsg_msg tmsg))) = true ->
        tmsg_info tmsg = None.
Proof.
  induction 1; simpl; intros; subst; [inv H1|].
  specialize (IHsteps eq_refl _ eq_refl).
  inv H0; [eauto| |].

  - simpl in H3.
    apply inMP_enqMP_or in H3; destruct H3.
    + subst; reflexivity.
    + eapply IHsteps; eauto.

  - simpl in H3.
    apply inMP_distributeMsgs_or in H3; destruct H3.
    + exfalso.
      unfold intOuts in H0; apply filter_In in H0; destruct H0.
      apply obj_in_sys_idx_internal in H1.
      destruct H13.
      clear -H0 H1 H3 H4.
      induction (rule_outs _ _ _); [inv H0|].
      inv H3; dest.
      inv H0.
      * simpl in H, H4.
        unfold id in H; rewrite H in H4.
        eapply internal_external_false; eauto.
      * eapply IHl; eauto.
    + eapply IHsteps; eauto.
      simpl.
      eapply inMP_deqMP; eauto.
Qed.

Lemma external_msg_in_tinfo:
  forall sys st,
    Reachable steps_det sys st ->
    forall from to chn tmsg msgs,
      msgs = tst_msgs st ->
      firstMP from to chn msgs = Some tmsg ->
      isExternal sys (mid_from (msg_id (tmsg_msg tmsg))) = true ->
      tmsg_info tmsg = None.
Proof.
  intros; inv H.
  eapply external_msg_in_tinfo'; eauto.
  eapply firstMP_inMP; eauto.
Qed.

Lemma internal_msg_in_tinfo':
  forall sys sti ll st,
    steps_det sys sti ll st ->
    sti = getStateInit sys ->
    forall msgs,
      msgs = tst_msgs st ->
      forall tmsg,
        InMP tmsg msgs ->
        isInternal sys (mid_from (msg_id (tmsg_msg tmsg))) = true ->
        exists tinfo, tmsg_info tmsg = Some tinfo.
Proof.
  induction 1; simpl; intros; subst; [inv H1|].
  specialize (IHsteps eq_refl _ eq_refl).
  inv H0; [eauto| |].

  - simpl in H3.
    apply inMP_enqMP_or in H3; destruct H3.
    + exfalso; subst; simpl in *.
      eauto using internal_external_false.
    + eapply IHsteps; eauto.

  - simpl in H3.
    apply inMP_distributeMsgs_or in H3; destruct H3.
    + clear -H0.
      unfold intOuts in H0; apply filter_In in H0; destruct H0.
      induction (rule_outs _ _ _); [inv H|].
      inv H; auto.
      simpl; eexists; reflexivity.
    + eapply IHsteps; eauto.
      simpl.
      eapply inMP_deqMP; eauto.
Qed.

Lemma internal_msg_in_tinfo:
  forall sys st,
    Reachable steps_det sys st ->
    forall from to chn tmsg msgs,
      msgs = tst_msgs st ->
      firstMP from to chn msgs = Some tmsg ->
      isInternal sys (mid_from (msg_id (tmsg_msg tmsg))) = true ->
      exists tinfo, tmsg_info tmsg = Some tinfo.
Proof.
  intros; inv H.
  eapply internal_msg_in_tinfo'; eauto.
  eapply firstMP_inMP; eauto.
Qed.

Lemma ts_monotone:
  forall sys st1 lbl st2,
    step_det sys st1 lbl st2 ->
    tst_tid st1 <= tst_tid st2.
Proof.
  intros; inv H; auto.
  simpl; destruct (tmsg_info fmsg); omega.
Qed.

Lemma reachable_hst_old':
  forall sys hst sti st,
    steps_det sys sti hst st ->
    sti = getStateInit sys ->
    Forall (fun tlbl =>
              match tlbl with
              | IlblOuts (Some hdl) _ =>
                match tmsg_info hdl with
                | Some tinfo => tinfo_tid tinfo <= tst_tid st
                | None => True
                end
              | _ => True
              end) hst.
Proof.
  induction 1; simpl; intros; subst; [constructor|].
  constructor.
  - assert (Reachable steps_det sys st2) by (econstructor; eauto).
    apply msgs_tinfo_old in H1.
    inv H0; simpl; auto.
    simpl in H1.
    apply firstMP_inMP in H6.
    eapply ForallMP_forall in H1; eauto.
    destruct (tmsg_info fmsg); auto.
  - apply ts_monotone in H0.
    specialize (IHsteps eq_refl).
    clear -H0 IHsteps.
    induction ll; simpl; intros; [constructor|].
    inv IHsteps.
    constructor; auto.
    destruct a; auto.
    destruct mhdl; auto.
    destruct (tmsg_info t); auto.
    omega.
Qed.

Lemma reachable_hst_old:
  forall sys st1,
    Reachable steps_det sys st1 ->
    forall hst st2,
      steps_det sys st1 hst st2 ->
      Forall (fun tlbl =>
                match tlbl with
                | IlblOuts (Some hdl) _ =>
                  match tmsg_info hdl with
                  | Some tinfo => tinfo_tid tinfo <= tst_tid st2
                  | None => True
                  end
                | _ => True
                end) hst.
Proof.
  intros; inv H.
  assert (steps_det sys (getStateInit sys) (hst ++ ll) st2).
  { eapply steps_append; eauto. }
  apply reachable_hst_old' in H; auto.
  apply Forall_app_inv in H.
  dest; auto.
Qed.

Lemma atomic_outs:
  forall sys rqin hst mouts orsout,
    Atomic sys rqin hst mouts orsout ->
    hst <> nil ->
    forall st1,
      Reachable steps_det sys st1 ->
      forall st2,
        steps_det sys st1 hst st2 ->
        trsMessages rqin (tst_msgs st2) = mouts.
Proof.
  induction 1; simpl; intros; [intuition idtac| |].
  - inv H6.
    pose proof (atomic_mouts_tinfo H H10) as Htinfo.
    eapply ForallMP_forall in Htinfo; eauto.
    inv H12; simpl in *.
    unfold distributeMsgs.
    rewrite trsMessages_app.
    destruct hst as [|lbl hst].

    + inv H10.
      clear IHAtomic; inv H.
      unfold InMP in H0; Common.dest_in.
      unfold toTMsg in H; cbn in H; inv H.
      eapply external_msg_in_tinfo in H14; eauto.
      rewrite H14 in *; clear H14.
      inv H9.
      f_equal.
      
      * pose proof (msgs_tinfo_old H5); simpl in H.
        replace (deqMP from to chn
                       (enqMP (toTMsg {| tinfo_tid := nts; tinfo_rqin := tmsg_msg fmsg |}
                                      (tmsg_msg fmsg)) nil))
          with (nil (A:= TMsg)).
        { (* NOTE: better to extract lemmas? *)
          clear -H Hts.
          assert (trsMessages {| tinfo_tid := nts; tinfo_rqin := tmsg_msg fmsg |} oims = nil).
          { induction oims; [reflexivity|].
            inv H; simpl.
            destruct (tmsg_info a); auto.
            destruct (tinfo_dec _ _); auto.
            subst; simpl in H2; omega.
          }
          pose proof (trsMessages_deqMP_SubList
                        {| tinfo_tid := nts; tinfo_rqin := tmsg_msg fmsg |}
                        fidx (obj_idx obj) fchn oims).
          rewrite H0 in H1.
          apply SubList_nil_inv in H1; auto.
        }
        { unfold deqMP, enqMP; simpl.
          apply firstMP_ValidMsgId in H3.
          rewrite <-H3; simpl.
          destruct (msgAddr_dec _ _); [|elim n; reflexivity].
          reflexivity.
        }
          
      * replace (intOuts sys (toTMsgs {| tinfo_tid := nts; tinfo_rqin := tmsg_msg fmsg |}
                                      (rule_outs frule os (msg_value (tmsg_msg fmsg)))))
          with (toTMsgs {| tinfo_tid := nts; tinfo_rqin := tmsg_msg fmsg |}
                        (rule_outs frule os (msg_value (tmsg_msg fmsg)))).
        { apply trsMessages_toTMsg. }
        { clear -H2.
          induction (toTMsgs {| tinfo_tid := nts; tinfo_rqin := tmsg_msg fmsg |}
                             (rule_outs frule os (msg_value (tmsg_msg fmsg))));
            [reflexivity|].
          inv H2; simpl; dest.
          rewrite H1.
          rewrite IHl at 1 by assumption; reflexivity.
        }

    + assert (exists tinfo, tmsg_info fmsg = Some tinfo).
      { inv H5.
        eapply internal_msg_in_tinfo; [| |eassumption|eassumption].
        { econstructor; eapply steps_append; eauto. }
        { reflexivity. }
      }
      destruct H6 as [tinfo ?]; rewrite H6 in *.
      inv Htinfo.
      assert (lbl :: hst <> nil) by discriminate.
      specialize (IHAtomic H7 _ H5 _ H10); clear H7; subst.
      apply trsMessages_In_tinfo in H0; inv H0.
      f_equal.
      * assert (from = fidx /\ to = obj_idx obj /\ chn = fchn).
        { apply firstMP_ValidMsgId in H3; apply firstMP_ValidMsgId in H14.
          unfold ValidMsgId in *; simpl in *.
          rewrite H3 in H14; inv H14; auto.
        }
        dest; subst; simpl.
        eapply trsMessages_deqMP_comm; eauto.
      * rewrite intOuts_Forall by assumption.
        apply trsMessages_toTMsg.

  - inv H4.
    pose proof (atomic_mouts_tinfo H H8) as Htinfo.
    eapply ForallMP_forall in Htinfo; [|left; reflexivity].
    inv H; [exfalso; eapply internal_external_false; eauto|].
    assert (IlblOuts (Some hdl0) houts :: hst0 <> nil) by discriminate.
    specialize (IHAtomic H _ H3 _ H8).
    clear H H2.
    inv H10; simpl in *.

    assert (exists tinfo, tmsg_info fmsg = Some tinfo).
    { inv H3.
      eapply internal_msg_in_tinfo; [| |eassumption|eassumption].
      { econstructor; eapply steps_append; eauto. }
      { reflexivity. }
    }
    destruct H as [tinfo ?]; rewrite H in *.
    inv Htinfo.

    rewrite H2.
    replace (intOuts sys (rsout :: nil)) with (nil (A:= TMsg))
      by (simpl; rewrite external_not_internal by assumption; reflexivity).
    unfold distributeMsgs; rewrite app_nil_r.

    rewrite trsMessages_deqMP_comm with (tmsg:= fmsg); try assumption.
    rewrite IHAtomic.
    simpl.
    apply firstMP_ValidMsgId in H16. inv H16.
    destruct (msgAddr_dec _ _); [|elim n; reflexivity].
    reflexivity.
Qed.

Corollary atomic_rs_out_trsMessages_nil:
  forall sys rqin hst mouts rsout,
    Atomic sys rqin hst mouts (Some rsout) ->
    forall st1,
      Reachable steps_det sys st1 ->
      forall st2,
        steps_det sys st1 hst st2 ->
        trsMessages rqin (tst_msgs st2) = nil.
Proof.
  intros.
  pose proof (atomic_rs_out_2 H); dest; subst.
  eapply atomic_outs; eauto.
Qed.

Theorem serializable_seqSteps_refines:
  forall sys,
    SerializableSys sys ->
    steps_det # seqSteps |-- sys ⊑[id] sys.
Proof.
  unfold SerializableSys, Refines; intros.
  inv H0; rename ll0 into ill.
  specialize (H _ _ H1).
  unfold Serializable in H.
  destruct H as [sll [sst [? ?]]].
  rewrite H0.
  econstructor; eauto.
  apply map_id.
Qed.

