Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepT SemFacts.

Set Implicit Arguments.

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

Definition msgAddrOf {MsgT} `{HasMsg MsgT} (msg: MsgT) :=
  mid_addr (msg_id (getMsg msg)).

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
  - inv H4.
    dest_equivT.
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
        { assert (NoDup
                    (map msgAddrOf
                         (intOuts
                            sys (toTMsgs match getTMsgsTInfo mins with
                                         | Some ti => ti
                                         | None => {| tinfo_tid := nts;
                                                      tinfo_rqin := map tmsg_msg mins |}
                                         end outs)))).
          { apply NoDup_map_filter.
            apply MsgAddr_NoDup_toTMsg.
            eapply ValidMsgOuts_MsgAddr_NoDup; eauto.
          }
          assert (NoDup ((map msgAddrOf [toTMsgU emsg0]))) by (repeat constructor; auto).
          assert (DisjList
                    (map msgAddrOf
                         (intOuts
                            sys (toTMsgs match getTMsgsTInfo mins with
                                         | Some ti => ti
                                         | None => {| tinfo_tid := nts;
                                                      tinfo_rqin := map tmsg_msg mins |}
                                         end outs)))
                    (map msgAddrOf [toTMsgU emsg0])).
          { assert (mid_from (msg_id (getMsg emsg0)) <> rule_oidx rule).
            { unfold fromExternal, isExternal in H2.
              intro Hx; rewrite Hx in H2.
              destruct (rule_oidx rule ?<n indicesOf sys); [discriminate|auto].
            }
            destruct H16.

            clear -H7 H8.
            induction outs; [apply DisjList_nil_1|].
            inv H8; specialize (IHouts H2); dest.
            unfold DisjList in *; intros.
            specialize (IHouts e); destruct IHouts; auto.
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

(* Lemma msg_outs_commutes: *)
(*   forall sys st1 orule1 mins1 mouts1 orule2 mins2 mouts2 st2, *)
(*     steps step_t sys st1 [RlblOuts orule1 mins1 mouts1; *)
(*                             RlblOuts orule2 mins2 mouts2] st2 -> *)
    
(*     DisjList (map msgAddrOf mouts2) (map msgAddrOf mins1) -> *)
(*     forall cst1, *)
(*       EquivTState st1 cst1 -> *)
(*       exists cst2, *)
(*         steps step_t sys cst1 [RlblOuts orule2 mins2 mouts2; *)
(*                                  RlblOuts orule1 mins1 mouts1] cst2 /\ *)
(*         EquivTState st2 cst2. *)
(* Proof. *)
(* Qed. *)
  
