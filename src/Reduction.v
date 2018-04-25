Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM SemFacts.

Set Implicit Arguments.

Ltac dest_step_m :=
  repeat match goal with
         | [H: steps step_m _ _ _ _ |- _] => inv H
         | [H: step_m _ _ _ _ |- _] => inv H
         | [H: {| bst_oss := _ |} = {| bst_oss := _ |} |- _] => inv H
         end; simpl in *.

Definition EquivMState (st1 st2: MState) :=
  bst_oss st1 = bst_oss st2 /\
  bst_orqs st1 = bst_orqs st2 /\
  EquivMP (bst_msgs st1) (bst_msgs st2).

Ltac dest_equivM :=
  repeat
    match goal with
    | [H: EquivMState _ _ |- _] => red in H; dest; simpl in *; subst
    | [H: ?t = ?t |- _] => clear H
    end.

Ltac split_equivM :=
  split; [|split]; simpl.

Lemma EquivMState_refl:
  forall st, EquivMState st st.
Proof.
  intros; split_equivM; auto.
  apply EquivMP_refl.
Qed.

Lemma EquivMState_sym:
  forall st1 st2, EquivMState st1 st2 -> EquivMState st2 st1.
Proof.
  intros; dest_equivM; split_equivM; auto.
  apply EquivMP_sym; auto.
Qed.

Lemma EquivMState_trans:
  forall st1 st2 st3,
    EquivMState st1 st2 ->
    EquivMState st2 st3 ->
    EquivMState st1 st3.
Proof.
  intros; dest_equivM; split_equivM.
  - rewrite H; auto.
  - rewrite H3; auto.
  - eapply EquivMP_trans; eauto.
Qed.

Lemma EquivMState_step_m:
  forall sys st1 lbl st2,
    step_m sys st1 lbl st2 ->
    forall cst1,
      EquivMState st1 cst1 ->
      exists cst2,
        step_m sys cst1 lbl cst2 /\ EquivMState st2 cst2.
Proof.
  intros.
  inv H.
  - exists cst1; split; auto.
    constructor.
  - destruct cst1 as [coss1 corqs1 cmsgs1].
    dest_equivM; eexists; split.
    + econstructor; eauto.
    + split_equivM; auto.
      apply EquivMP_enqMP; auto.
  - destruct cst1 as [coss1 corqs1 cmsgs1].
    dest_equivM; eexists; split.
    + econstructor; try reflexivity; try eassumption.
      eapply EquivMP_Forall_FirstMP; eauto.
    + split_equivM; auto.
      apply EquivMP_distributeMsgs.
      apply EquivMP_removeMsgs.
      auto.
Qed.

Lemma EquivMState_steps_t:
  forall sys st1 hst st2,
    steps step_m sys st1 hst st2 ->
    forall cst1,
      EquivMState st1 cst1 ->
      exists cst2,
        steps step_m sys cst1 hst cst2 /\ EquivMState st2 cst2.
Proof.
  induction 1; simpl; intros.
  - exists cst1; split; auto.
    constructor.
  - specialize (IHsteps _ H1); destruct IHsteps as [csti [? ?]].
    eapply EquivMState_step_m in H0; eauto.
    destruct H0 as [cst2 [? ?]].
    eexists; split.
    + econstructor; eassumption.
    + assumption.
Qed.

Definition msgAddrOf (msg: Msg) :=
  mid_addr (msg_id msg).

Definition NonSilentHistory (hst: History) :=
  Forall (fun lbl => lbl <> emptyRLabel) hst.

Definition NotMsgIn (lbl: MLabel) :=
  match lbl with
  | RlblIn _ => False
  | _ => True
  end.

Definition NonMsgInHistory (hst: History) :=
  Forall (fun tlbl => NotMsgIn tlbl) hst.

Lemma msg_in_commutes:
  forall sys st1 emsg lbl st2,
    NotMsgIn lbl ->
    steps step_m sys st1 [RlblIn emsg; lbl] st2 ->
    forall cst1,
      EquivMState st1 cst1 ->
      exists cst2,
        steps step_m sys cst1 [lbl; RlblIn emsg] cst2 /\
        EquivMState st2 cst2.
Proof.
  intros.
  destruct lbl as [|hdl mins mouts]; [elim H|].
  destruct cst1 as [coss1 corqs1 cmsgs1].
  dest_step_m.
  - eexists; split.
    + repeat econstructor; eauto.
    + dest_equivM.
      repeat split.
      apply EquivMP_enqMP; auto.
  - dest_equivM.
    eexists; split.
    + econstructor.
      * repeat econstructor; eauto.
      * econstructor; try reflexivity; try eassumption.
        clear -H4 H10; eapply Forall_impl.
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
        { assert (NoDup (map msgAddrOf (intOuts sys mouts))).
          { apply NoDup_map_filter.
            eapply ValidMsgOuts_MsgAddr_NoDup in H17; eauto.
          }
          assert (NoDup ((map msgAddrOf [emsg])))
            by (repeat constructor; auto).
          assert (DisjList
                    (map msgAddrOf (intOuts sys mouts))
                    (map msgAddrOf [emsg])).
          { assert (mid_from (msg_id emsg) <> rule_oidx rule).
            { unfold fromExternal, isExternal in H2.
              simpl in H2; unfold id in H2.
              intro Hx; rewrite Hx in H2.
              destruct (rule_oidx rule ?<n sys_inds sys); [discriminate|auto].
            }
            destruct H17.

            clear -H7 H8.
            induction mouts; [apply DisjList_nil_1|].
            inv H8; specialize (IHmouts H2); dest.
            unfold DisjList in *; intros.
            specialize (IHmouts e); destruct IHmouts; auto.
            destruct (ma_from e ==n rule_oidx rule).
            { right; intro Hx; Common.dest_in; auto. }
            { left; intro Hx; simpl in Hx.
              destruct (toInternal sys _); auto.
              inv Hx; auto.
            }
          }

          apply EquivMP_MsgAddr_NoDup_EquivList.
          { rewrite map_app; apply NoDup_DisjList; auto. }
          { rewrite map_app; apply NoDup_DisjList; auto.
            apply DisjList_comm; auto.
          }
          { apply EquivList_app_comm. }
        }
      * eapply ValidMsgsIn_MsgAddr_NoDup; eauto.        
      * eapply EquivMP_Forall_FirstMP; eauto.
Qed.

Lemma msg_in_reduced:
  forall sys st1 emsg hst2 st2,
    steps step_m sys st1 (RlblIn emsg :: hst2) st2 ->
    NonMsgInHistory hst2 ->
    forall cst1,
      EquivMState st1 cst1 ->
      exists cst2,
        steps step_m sys cst1 (hst2 ++ [RlblIn emsg]) cst2 /\
        EquivMState st2 cst2.
Proof.
  induction hst2 as [|lbl ?]; simpl; intros.
  - dest_step_m.
    destruct cst1 as [coss1 corqs1 cmsgs1].
    exists {| bst_oss := coss1; bst_orqs := corqs1;
              bst_msgs := enqMP emsg cmsgs1 |}; split.
    + repeat econstructor; eauto.
    + dest_equivM; split_equivM; auto.
      apply EquivMP_enqMP; auto.
      
  - inv H0.
    change (RlblIn emsg :: lbl :: hst2) with ([RlblIn emsg; lbl] ++ hst2) in H.
    eapply steps_split in H; [|reflexivity].
    destruct H as [sti [? ?]].
    eapply msg_in_commutes in H0; [|assumption|apply EquivMState_refl].
    destruct H0 as [cst2 [? ?]].
    pose proof (steps_append H H0); inv H3.
    specialize (IHhst2 _ H9 H5 _ H1).
    destruct IHhst2 as [icst2 [? ?]].
    eapply EquivMState_step_m in H11; [|eassumption].
    destruct H11 as [cst3 [? ?]].
    exists cst3; split.
    + econstructor; eauto.
    + eapply EquivMState_trans; eauto.
Qed.

Lemma msg_in_reduced_app:
  forall sys st1 hst1 emsg hst2 st2,
    steps step_m sys st1 (hst1 ++ RlblIn emsg :: hst2) st2 ->
    NonMsgInHistory hst2 ->
    forall cst1,
      EquivMState st1 cst1 ->
      exists cst2,
        steps step_m sys cst1 (hst1 ++ hst2 ++ [RlblIn emsg]) cst2 /\
        EquivMState st2 cst2.
Proof.
  intros.
  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  eapply msg_in_reduced in H; eauto.
  destruct H as [csti [? ?]].
  eapply EquivMState_steps_t in H2; eauto.
  destruct H2 as [cst2 [? ?]].
  exists cst2; split.
  - eapply steps_append; eauto.
  - assumption.
Qed.

Definition NonInterfering (rule1 rule2: Rule)
           (mins1 mins2 mouts1 mouts2: list Msg) :=
  rule_oidx rule1 <> rule_oidx rule2 /\
  DisjList (map msgAddrOf mins1) (map msgAddrOf mins2) /\
  DisjList (map msgAddrOf mouts1) (map msgAddrOf mins2).

Lemma msg_outs_commutes:
  forall sys st1 rule1 mins1 mouts1 rule2 mins2 mouts2 st2,
    steps step_m sys st1 [RlblOuts (Some rule1) mins1 mouts1;
                            RlblOuts (Some rule2) mins2 mouts2] st2 ->
    NonInterfering rule1 rule2 mins1 mins2 mouts1 mouts2 ->
    forall cst1,
      EquivMState st1 cst1 ->
      exists cst2,
        steps step_m sys cst1 [RlblOuts (Some rule2) mins2 mouts2;
                                 RlblOuts (Some rule1) mins1 mouts1] cst2 /\
        EquivMState st2 cst2.
Proof.
  intros.
  destruct cst1 as [coss1 corqs1 cmsgs1].
  dest_step_m.
  dest_equivM.
  destruct H0 as [? [? ?]].
  eexists; split.
  - econstructor.
    + econstructor.
      * econstructor.
      * econstructor; try reflexivity; try eassumption.
        { findeq. }
        { findeq. }
        { admit. }
    + econstructor; try reflexivity; try eassumption.
      { findeq. }
      { findeq. }
      { admit. }
  - split_equivM.
    + meq.
    + meq.
    + admit.
        
Admitted.



