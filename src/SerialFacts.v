Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap.
Require Import Syntax Semantics SemFacts StepT Serial Invariant.

Require Import Omega.
Require Import Program.Equality.

Set Implicit Arguments.

Lemma atomic_emptyILabel_not_in:
  forall sys ts rq hst mouts,
    Atomic sys ts rq hst mouts ->
    ~ In emptyRLabel hst.
Proof.
  induction 1; simpl; intros.
  - intro Hx; destruct Hx; [discriminate|auto].
  - intro Hx; destruct Hx; auto.
    inv H2; elim H0; reflexivity.
Qed.

Lemma atomic_iLblIn_not_in:
  forall sys ts rq hst mouts,
    Atomic sys ts rq hst mouts ->
    forall msg,
      ~ In (RlblIn msg) hst.
Proof.
  induction 1; simpl; intros; [auto|];
    try (intro Hx; destruct Hx;
         [discriminate|firstorder]).
Qed.

Lemma atomic_preserved:
  forall impl1 ts rq hst mouts,
    Atomic impl1 ts rq hst mouts ->
    forall impl2,
      indicesOf impl1 = indicesOf impl2 ->
      Atomic impl2 ts rq hst mouts.
Proof.
  induction 1; simpl; intros.
  - econstructor; eauto.
    unfold fromExternal, isExternal in *; simpl in *.
    rewrite H1 in H; assumption.
  - econstructor; eauto.
Qed.

Lemma atomic_tinfo:
  forall sys ts rq hst mouts,
    Atomic sys ts rq hst mouts ->
    forall st1 st2,
      steps step_t sys st1 hst st2 ->
      Forall (fun lbl => match lbl with
                         | RlblOuts _ ins outs =>
                           Forall (fun tmsg =>
                                     match tmsg_info tmsg with
                                     | Some hti =>
                                       hti = buildTInfo ts [rq] /\
                                       fromInternal sys tmsg = true
                                     | None =>
                                       tmsg_msg tmsg = rq /\
                                       fromExternal sys tmsg = true
                                     end) ins /\
                           Forall (fun tmsg =>
                                     tmsg_info tmsg = Some (buildTInfo ts [rq])) outs
                         | _ => False
                         end) hst /\
      ForallMP (fun tmsg =>
                  tmsg_info tmsg = Some (buildTInfo ts [rq]) /\
                  fromInternal sys tmsg = true) mouts.
Proof.
  induction 1; simpl; intros.

  - split.
    + constructor; auto.
      split; auto.
      constructor; cbn; auto.
    + inv H1; inv H5; inv H7.
      apply idx_in_sys_internal in H4.
      apply validMsgOuts_from_internal with (sys0:= sys) in H13; [|assumption].
      clear -H0 H13.
      induction outs; simpl; [constructor|].
      inv H0; inv H13.
      constructor; auto.
      eapply IHouts; eauto.

  - inv H2.
    specialize (IHAtomic _ _ H6); destruct IHAtomic.
    split.
    + constructor; auto.
      assert (Forall (fun tmsg =>
                        tmsg_info tmsg = Some (buildTInfo ts [rq]) /\
                        fromInternal sys tmsg = true) msgs).
      { eapply ForallMP_SubList; eauto. }
      
      split.
      * clear -H4; eapply Forall_impl; eauto.
        simpl; intros.
        destruct H; rewrite H, H0; auto.
      * inv H8.
        assert (Forall (fun tmsg : TMsg =>
                          tmsg_info tmsg = Some (buildTInfo ts [rq])) msgs).
        { clear -H4; eapply Forall_impl; eauto.
          simpl; intros.
          destruct H; auto.
        }
        erewrite getTMsgsTInfo_Forall_Some; eauto.
        clear; induction outs; constructor; auto.
        
    + apply ForallMP_distributeMsgs.
      * apply ForallMP_removeMsgs; auto.
      * eapply ForallMP_SubList in H1; eauto.
        inv H8.
        destruct msgs as [|msg msgs]; [elim H0; reflexivity|].
        inv H1; cbn; destruct H7; rewrite H1.
        apply idx_in_sys_internal in H9.
        apply validMsgOuts_from_internal with (sys0:= sys) in H17; [|assumption].
        clear -H17.
        induction outs; [constructor|].
        inv H17.
        constructor; auto.
        eapply IHouts; eauto.
Qed.

Corollary atomic_hst_tinfo:
  forall sys ts rq hst mouts,
    Atomic sys ts rq hst mouts ->
    forall st1 st2,
      steps step_t sys st1 hst st2 ->
      Forall (fun lbl => match lbl with
                         | RlblOuts _ ins outs =>
                           Forall (fun tmsg =>
                                     match tmsg_info tmsg with
                                     | Some hti =>
                                       hti = buildTInfo ts (rq :: nil) /\
                                       fromInternal sys tmsg = true
                                     | None =>
                                       tmsg_msg tmsg = rq /\
                                       fromExternal sys tmsg = true
                                     end) ins /\
                           Forall (fun tmsg =>
                                     tmsg_info tmsg = Some (buildTInfo ts [rq])) outs
                         | _ => False
                         end) hst.
Proof.
  intros.
  eapply atomic_tinfo in H; eauto.
  destruct H; auto.
Qed.

Corollary atomic_mouts_tinfo:
  forall sys ts rq hst mouts,
    Atomic sys ts rq hst mouts ->
    forall st1 st2,
      steps step_t sys st1 hst st2 ->
      ForallMP (fun tmsg => tmsg_info tmsg = Some (buildTInfo ts (rq :: nil)) /\
                            fromInternal sys tmsg = true) mouts.
Proof.
  intros.
  eapply atomic_tinfo in H; eauto.
  destruct H; auto.
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

Theorem serializable_seqSteps_refines:
  forall sys,
    SerializableSys sys ->
    steps step_t # seqSteps |-- sys ⊑[id] sys.
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

