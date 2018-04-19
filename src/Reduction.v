Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepT SemFacts.

(*! TODO: move the below section to MessagePool.v *)

Set Implicit Arguments.

Lemma hd_error_Some_app:
  forall {A} (l1: list A) v,
    hd_error l1 = Some v ->
    forall l2,
      hd_error (l1 ++ l2) = Some v.
Proof.
  destruct l1; intros; [discriminate|].
  simpl in H; inv H.
  reflexivity.
Qed.

Section Facts.
  Variable (MsgT: Type).
  Context `{HasMsg MsgT}.

  Lemma findMP_nil:
    forall mp,
      (forall from to chn, findMP from to chn mp = nil) ->
      mp = nil.
  Proof.
    intros.
    destruct mp as [|msg ?]; auto.
    exfalso.
    specialize (H0 (mid_from (msg_id (getMsg msg)))
                   (mid_to (msg_id (getMsg msg)))
                   (mid_chn (msg_id (getMsg msg)))).
    simpl in H0.
    unfold isAddrOf in H0.
    destruct (msgAddr_dec _ _); [discriminate|].
    elim n.
    destruct (getMsg msg) as [[[from to chn] tid] val]; cbn in *.
    reflexivity.
  Qed.

  Lemma findMP_app:
    forall from to chn mp1 mp2,
      findMP from to chn (mp1 ++ mp2) =
      findMP from to chn mp1 ++ findMP from to chn mp2.
  Proof.
    unfold findMP; intros.
    apply filter_app.
  Qed.

  Corollary findMP_enqMP:
    forall from to chn mp msg,
      findMP from to chn (enqMP msg mp) =
      findMP from to chn mp ++ findMP from to chn [msg].
  Proof.
    unfold enqMP; intros.
    apply findMP_app.
  Qed.

  Lemma FirstMP_enqMP:
    forall mp msg,
      FirstMP mp msg ->
      forall emsg,
        FirstMP (enqMP emsg mp) msg.
  Proof.
    unfold FirstMP, firstMP, enqMP; intros.
    rewrite findMP_app.
    apply hd_error_Some_app; auto.
  Qed.

  Lemma findMP_deqMP_eq:
    forall from to chn mp,
      findMP from to chn (deqMP from to chn mp) =
      deqMP from to chn (findMP from to chn mp).
  Proof.
    induction mp; simpl; intros; [reflexivity|].
    unfold isAddrOf; destruct (msgAddr_dec _ _).
    - simpl; unfold isAddrOf.
      destruct (msgAddr_dec _ _); auto.
      elim n; assumption.
    - simpl; unfold isAddrOf.
      destruct (msgAddr_dec _ _); auto.
      elim n; assumption.
  Qed.

  Lemma findMP_deqMP_neq:
    forall from to chn dfrom dto dchn mp,
      buildMsgAddr from to chn <> buildMsgAddr dfrom dto dchn ->
      findMP from to chn (deqMP dfrom dto dchn mp) =
      findMP from to chn mp.
  Proof.
    induction mp; intros; [reflexivity|].
    simpl; unfold isAddrOf.
    destruct (msgAddr_dec _ _).
    - destruct (msgAddr_dec _ _); auto.
      rewrite e0 in e; elim H0; assumption.
    - simpl; unfold isAddrOf.
      destruct (msgAddr_dec _ _); auto.
      rewrite e in n.
      erewrite IHmp; eauto.
  Qed.

  Lemma firstMP_deqMP_app:
    forall mp1 from to chn,
      firstMP from to chn mp1 <> None ->
      forall mp2,
        deqMP from to chn (mp1 ++ mp2) =
        deqMP from to chn mp1 ++ mp2.
  Proof.
    induction mp1; simpl; intros; [elim H0; reflexivity|].
    unfold isAddrOf; destruct (msgAddr_dec _ _); auto.
    simpl; rewrite IHmp1; [reflexivity|].
    assert (exists v, firstMP from to chn ([a] ++ mp1) = Some v).
    { simpl.
      destruct (firstMP from to chn (a :: mp1)); [|exfalso; auto].
      eexists; reflexivity.
    }
    destruct H1 as [v ?].
    apply firstMP_app_or in H1; destruct H1.
    - exfalso.
      unfold firstMP, findMP, isAddrOf in H1; simpl in H1.
      destruct (msgAddr_dec _ _); auto.
      discriminate.
    - rewrite H1; discriminate.
  Qed.

  Lemma FirstMP_deqMP_enqMP_comm:
    forall mp from to chn emsg,
      firstMP from to chn mp <> None ->
      deqMP from to chn (enqMP emsg mp) =
      enqMP emsg (deqMP from to chn mp).
  Proof.
    unfold enqMP; intros.
    apply firstMP_deqMP_app; auto.
  Qed.    

  Lemma FirstMP_removeMP_enqMP_comm:
    forall mp rmsg,
      FirstMP mp rmsg ->
      forall emsg,
        removeMP rmsg (enqMP emsg mp) =
        enqMP emsg (removeMP rmsg mp).
  Proof.
    unfold removeMP; intros.
    apply FirstMP_deqMP_enqMP_comm.
    rewrite H0; discriminate.
  Qed.

  Lemma firstMP'_firstMP'_removeMP:
    forall mp from1 to1 chn1 msg1 from2 to2 chn2 msg2,
      buildMsgAddr from1 to1 chn1 <> buildMsgAddr from2 to2 chn2 ->
      firstMP' from1 to1 chn1 mp = Some msg1 ->
      firstMP' from2 to2 chn2 mp = Some msg2 ->
      firstMP' from2 to2 chn2 (removeMP msg1 mp) = Some msg2.
  Proof.
    intros.
    pose proof H1; rewrite <-firstMP_firstMP' in H3.
    apply firstMP_MsgAddr in H3.
    pose proof H2; rewrite <-firstMP_firstMP' in H4.
    apply firstMP_MsgAddr in H4.
    induction mp; simpl; intros; [discriminate|].
    cbn in *.
    remember (getMsg msg1) as m1.
    destruct m1 as [[[mfrom1 mto1 mchn1] mtid1] mval1]; cbn in *.
    remember (getMsg msg2) as m2.
    destruct m2 as [[[mfrom2 mto2 mchn2] mtid2] mval2]; cbn in *.
    inv H3; inv H4.
    unfold isAddrOf in *.
    destruct (msgAddr_dec _ _).
    - destruct (msgAddr_dec _ _); auto.
      exfalso; inv H1; inv H2.
      rewrite e in e0; auto.
    - simpl; unfold isAddrOf.
      destruct (msgAddr_dec _ _); auto.
      specialize (IHmp H1 H2).
      erewrite removeMP_deqMP in IHmp by reflexivity.
      rewrite <-Heqm1 in IHmp.
      assumption.
  Qed.
    
  Lemma FirstMP_FirstMP_removeMP:
    forall mp msg1 msg2,
      mid_addr (msg_id (getMsg msg1)) <> mid_addr (msg_id (getMsg msg2)) ->
      FirstMP mp msg1 ->
      FirstMP mp msg2 ->
      FirstMP (removeMP msg1 mp) msg2.
  Proof.
    unfold FirstMP; intros.
    rewrite firstMP_firstMP' in *.
    induction mp; simpl; intros; [inv H1|].
    inv H1.
    unfold FirstMP in *; intros.
    eapply firstMP'_firstMP'_removeMP; eauto.
    destruct (getMsg msg1) as [[[mfrom1 mto1 mchn1] mtid1] mval1]; cbn in *.
    destruct (getMsg msg2) as [[[mfrom2 mto2 mchn2] mtid2] mval2]; cbn in *.
    auto.
  Qed.

  Corollary FirstMP_Forall_FirstMP_removeMP:
    forall mp msg1 msgs2,
      Forall (fun msg2 => mid_addr (msg_id (getMsg msg1)) <>
                          mid_addr (msg_id (getMsg msg2))) msgs2 ->
      FirstMP mp msg1 ->
      Forall (FirstMP mp) msgs2 ->
      Forall (FirstMP (removeMP msg1 mp)) msgs2.
  Proof.
    induction msgs2; simpl; intros; [constructor|].
    inv H0; inv H2.
    constructor; auto.
    apply FirstMP_FirstMP_removeMP; auto.
  Qed.

  Lemma FirstMP_removeMsgs_enqMP_comm:
    forall msgs mp,
      NoDup (map (fun msg => mid_addr (msg_id (getMsg msg))) msgs) ->
      Forall (FirstMP mp) msgs ->
      forall msg,
        removeMsgs msgs (enqMP msg mp) =
        enqMP msg (removeMsgs msgs mp).
  Proof.
    induction msgs; simpl; intros; [reflexivity|].
    inv H0; inv H1.
    rewrite FirstMP_removeMP_enqMP_comm by assumption.
    rewrite <-IHmsgs; [reflexivity|assumption|].
    apply FirstMP_Forall_FirstMP_removeMP; auto.

    clear -H4.
    induction msgs; [constructor|].
    constructor.
    - intro Hx; elim H4; left; auto.
    - eapply IHmsgs.
      intro Hx; elim H4; right; auto.
  Qed.

End Facts.

Section EquivMPFacts.
  Variable (MsgT: Type).
  Context `{HasMsg MsgT}.

  Lemma EquivMP_refl:
    forall mp, EquivMP mp mp.
  Proof.
    unfold EquivMP; intros; reflexivity.
  Qed.

  Lemma EquivMP_sym:
    forall mp1 mp2, EquivMP mp1 mp2 -> EquivMP mp2 mp1.
  Proof.
    unfold EquivMP; intros; auto.
  Qed.

  Lemma EquivMP_trans:
    forall mp1 mp2 mp3,
      EquivMP mp1 mp2 ->
      EquivMP mp2 mp3 ->
      EquivMP mp1 mp3.
  Proof.
    unfold EquivMP; intros.
    rewrite H0; auto.
  Qed.

  Lemma EquivMP_enqMP:
    forall mp1 mp2,
      EquivMP mp1 mp2 ->
      forall msg,
        EquivMP (enqMP msg mp1) (enqMP msg mp2).
  Proof.
    unfold EquivMP; intros.
    do 2 rewrite findMP_enqMP.
    rewrite H0; reflexivity.
  Qed.

  Lemma EquivMP_FirstMP:
    forall mp1 mp2,
      EquivMP mp1 mp2 ->
      forall msg,
        FirstMP mp1 msg ->
        FirstMP mp2 msg.
  Proof.
    unfold EquivMP, FirstMP, firstMP; intros.
    rewrite <-H0; assumption.
  Qed.

  Corollary EquivMP_Forall_FirstMP:
    forall mp1 mp2,
      EquivMP mp1 mp2 ->
      forall msgs,
        Forall (FirstMP mp1) msgs ->
        Forall (FirstMP mp2) msgs.
  Proof.
    intros.
    eapply Forall_impl; [|eassumption].
    intros.
    eapply EquivMP_FirstMP; eauto.
  Qed.

  Lemma EquivMP_distributeMsgs:
    forall mp1 mp2,
      EquivMP mp1 mp2 ->
      forall msgs,
        EquivMP (distributeMsgs msgs mp1) (distributeMsgs msgs mp2).
  Proof.
    unfold EquivMP, distributeMsgs; intros.
    do 2 rewrite findMP_app.
    rewrite H0; reflexivity.
  Qed.

  Lemma EquivMP_deqMP:
    forall mp1 mp2,
      EquivMP mp1 mp2 ->
      forall from to chn,
        EquivMP (deqMP from to chn mp1) (deqMP from to chn mp2).
  Proof.
    unfold EquivMP; intros.
    destruct (msgAddr_dec (buildMsgAddr from0 to0 chn0) (buildMsgAddr from to chn)).
    - inv e.
      do 2 rewrite findMP_deqMP_eq.
      rewrite H0; reflexivity.
    - do 2 rewrite findMP_deqMP_neq by assumption.
      auto.
  Qed.

  Lemma EquivMP_removeMP:
    forall mp1 mp2,
      EquivMP mp1 mp2 ->
      forall msg,
        EquivMP (removeMP msg mp1) (removeMP msg mp2).
  Proof.
    intros; apply EquivMP_deqMP; auto.
  Qed.

  Lemma EquivMP_removeMsgs:
    forall msgs mp1 mp2,
      EquivMP mp1 mp2 ->
      EquivMP (removeMsgs msgs mp1) (removeMsgs msgs mp2).
  Proof.
    induction msgs; intros; auto.
    simpl.
    apply IHmsgs.
    apply EquivMP_removeMP.
    auto.
  Qed.

  Lemma EquivMP_app:
    forall mp1 mp2,
      EquivMP mp1 mp2 ->
      forall mp3 mp4,
        EquivMP mp3 mp4 ->
        EquivMP (mp1 ++ mp3) (mp2 ++ mp4).
  Proof.
    unfold EquivMP; intros.
    do 2 rewrite findMP_app.
    rewrite H0, H1; reflexivity.
  Qed.

End EquivMPFacts.

Definition EquivTState (tst1 tst2: TState) :=
  tst_oss tst1 = tst_oss tst2 /\
  tst_orqs tst1 = tst_orqs tst2 /\
  EquivMP (tst_msgs tst1) (tst_msgs tst2) /\
  tst_tid tst1 = tst_tid tst2.

Ltac dest_equivT :=
  repeat
    match goal with
    | [H: EquivTState _ _ |- _] => red in H; dest; simpl in *; subst
    | [H: ?t = ?t |- _] => clear H
    end.

Ltac split_equivT :=
  split; [|split; [|split]]; simpl.

Lemma EquivTState_refl:
  forall tst, EquivTState tst tst.
Proof.
  intros; split_equivT; auto.
  apply EquivMP_refl.
Qed.

Lemma EquivTState_sym:
  forall tst1 tst2, EquivTState tst1 tst2 -> EquivTState tst2 tst1.
Proof.
  intros; dest_equivT; split_equivT; auto.
  apply EquivMP_sym; auto.
Qed.

Lemma EquivTState_trans:
  forall tst1 tst2 tst3,
    EquivTState tst1 tst2 ->
    EquivTState tst2 tst3 ->
    EquivTState tst1 tst3.
Proof.
  intros; dest_equivT; split_equivT.
  - rewrite H; auto.
  - rewrite H4; auto.
  - eapply EquivMP_trans; eauto.
  - rewrite H6; auto.
Qed.

Lemma EquivTState_step_t:
  forall sys st1 lbl st2,
    step_t sys st1 lbl st2 ->
    forall cst1,
      EquivTState st1 cst1 ->
      exists cst2,
        step_t sys cst1 lbl cst2 /\ EquivTState st2 cst2.
Proof.
  intros.
  inv H.
  - exists cst1; split; auto.
    constructor.
  - destruct cst1 as [coss1 corqs1 cmsgs1 cts1].
    dest_equivT; eexists; split.
    + econstructor; eauto.
    + split_equivT; auto.
      apply EquivMP_enqMP; auto.
  - destruct cst1 as [coss1 corqs1 cmsgs1 cts1].
    dest_equivT; eexists; split.
    + econstructor; try reflexivity; try eassumption.
      eapply EquivMP_Forall_FirstMP; eauto.
    + split_equivT; auto.
      apply EquivMP_distributeMsgs.
      apply EquivMP_removeMsgs.
      auto.
Qed.

Lemma EquivTState_steps_t:
  forall sys st1 hst st2,
    steps step_t sys st1 hst st2 ->
    forall cst1,
      EquivTState st1 cst1 ->
      exists cst2,
        steps step_t sys cst1 hst cst2 /\ EquivTState st2 cst2.
Proof.
  induction 1; simpl; intros.
  - exists cst1; split; auto.
    constructor.
  - specialize (IHsteps _ H1); destruct IHsteps as [csti [? ?]].
    eapply EquivTState_step_t in H0; eauto.
    destruct H0 as [cst2 [? ?]].
    eexists; split.
    + econstructor; eassumption.
    + assumption.
Qed.

Definition NonSilentHistory (hst: THistory) :=
  Forall (fun tlbl => tlbl <> emptyRLabel) hst.

Definition NotMsgIn {MsgT} (lbl: RLabel MsgT) :=
  match lbl with
  | RlblIn _ => False
  | _ => True
  end.

Definition NonMsgInHistory (hst: THistory) :=
  Forall (fun tlbl => NotMsgIn tlbl) hst.

Ltac dest_step_t :=
  repeat match goal with
         | [H: steps step_t _ _ _ _ |- _] => inv H
         | [H: step_t _ _ _ _ |- _] => inv H
         end; simpl in *.

Lemma msg_in_commutes:
  forall sys st1 emsg tlbl st2,
    NotMsgIn tlbl ->
    steps step_t sys st1 [RlblIn emsg; tlbl] st2 ->
    forall cst1,
      EquivTState st1 cst1 ->
      exists cst2,
        steps step_t sys cst1 [tlbl; RlblIn emsg] cst2 /\
        EquivTState st2 cst2.
Proof.
  intros.
  destruct tlbl as [|hdl mins mouts]; [elim H|].
  destruct cst1 as [coss1 corqs1 cmsgs1 cts1].
  dest_step_t.
  - eexists; split.
    + repeat econstructor; eauto.
    + dest_equivT.
      repeat split.
      apply EquivMP_enqMP; auto.
  - inv H8.
    dest_equivT.
    eexists; split.
    + econstructor.
      * repeat econstructor; eauto.
      * econstructor; try reflexivity; try eassumption.
        clear -H7 H9; eapply Forall_impl.
        { clear; intros; simpl in H.
          apply FirstMP_enqMP; eassumption.
        }
        { eapply Forall_impl; [|eassumption].
          intros.
          eapply EquivMP_FirstMP; eauto.
        }
    + repeat split; simpl.
      rewrite FirstMP_removeMsgs_enqMP_comm.
      * unfold enqMP, distributeMsgs.
        do 2 rewrite <-app_assoc.
        apply EquivMP_app.
        { apply EquivMP_removeMsgs; auto. }
        { admit. }
      * eapply ValidMsgsIn_MsgAddr_NoDup; eauto.        
      * eapply EquivMP_Forall_FirstMP; eauto.
Admitted.

Lemma msg_in_reduced:
  forall sys st1 emsg hst2 st2,
    steps step_t sys st1 (RlblIn emsg :: hst2) st2 ->
    NonMsgInHistory hst2 ->
    forall cst1,
      EquivTState st1 cst1 ->
      exists cst2,
        steps step_t sys cst1 (hst2 ++ [RlblIn emsg]) cst2 /\
        EquivTState st2 cst2.
Proof.
  induction hst2 as [|tlbl ?]; simpl; intros.
  - dest_step_t.
    destruct cst1 as [coss1 corqs1 cmsgs1 cts1].
    exists {| tst_oss := coss1; tst_orqs := corqs1;
              tst_msgs := enqMP (toTMsgU emsg0) cmsgs1; tst_tid := cts1 |}; split.
    + repeat econstructor; eauto.
    + dest_equivT; split_equivT; auto.
      apply EquivMP_enqMP; auto.
      
  - inv H0.
    change (RlblIn emsg :: tlbl :: hst2) with ([RlblIn emsg; tlbl] ++ hst2) in H.
    eapply steps_split in H; [|reflexivity].
    destruct H as [sti [? ?]].
    eapply msg_in_commutes in H0; [|assumption|apply EquivTState_refl].
    destruct H0 as [cst2 [? ?]].
    pose proof (steps_append H H0); inv H3.
    specialize (IHhst2 _ H9 H5 _ H1).
    destruct IHhst2 as [icst2 [? ?]].
    eapply EquivTState_step_t in H11; [|eassumption].
    destruct H11 as [cst3 [? ?]].
    exists cst3; split.
    + econstructor; eauto.
    + eapply EquivTState_trans; eauto.
Qed.

Lemma msg_in_reduced_app:
  forall sys st1 hst1 emsg hst2 st2,
    steps step_t sys st1 (hst1 ++ RlblIn emsg :: hst2) st2 ->
    NonMsgInHistory hst2 ->
    forall cst1,
      EquivTState st1 cst1 ->
      exists cst2,
        steps step_t sys cst1 (hst1 ++ hst2 ++ [RlblIn emsg]) cst2 /\
        EquivTState st2 cst2.
Proof.
  intros.
  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  eapply msg_in_reduced in H; eauto.
  destruct H as [csti [? ?]].
  eapply EquivTState_steps_t in H2; eauto.
  destruct H2 as [cst2 [? ?]].
  exists cst2; split.
  - eapply steps_append; eauto.
  - assumption.
Qed.

