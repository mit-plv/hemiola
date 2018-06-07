Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM SemFacts.
Require Import Topology Serial SerialFacts.

Set Implicit Arguments.

Ltac dest_step_m :=
  repeat match goal with
         | [H: steps step_m _ _ _ _ |- _] => inv H
         | [H: step_m _ _ _ _ |- _] => inv H
         | [H: {| bst_oss := _ |} = {| bst_oss := _ |} |- _] => inv H
         end; simpl in *.

Definition NonSilentHistory (hst: MHistory) :=
  Forall (fun lbl => lbl <> RlblEmpty _) hst.

Definition Internal (lbl: MLabel) :=
  match lbl with
  | RlblInt _ _ _ => True
  | _ => False
  end.

Definition InternalHistory (hst: MHistory) :=
  Forall (fun tlbl => Internal tlbl) hst.

Definition Reduced (sys: System) (hfr hto: MHistory) :=
  forall st1 st2,
    steps step_m sys st1 hfr st2 ->
    steps step_m sys st1 hto st2 /\
    BEquivalent sys hfr hto.

(*! General Facts *)

Lemma atomic_internal_history:
  forall inits ins hst outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
    InternalHistory hst.
Proof.
  induction 1; simpl; intros.
  - repeat constructor.
  - repeat constructor; auto.
Qed.

Lemma internal_history_behavior_nil:
  forall sys hst,
    InternalHistory hst -> behaviorOf sys hst = nil.
Proof.
  induction hst; simpl; intros; auto.
  inv H; rewrite IHhst by assumption.
  destruct a; auto; elim H2.
Qed.

Lemma reduced_refl:
  forall sys hst, Reduced sys hst hst.
Proof.
  unfold Reduced; intros.
  split; auto.
  congruence.
Qed.

Lemma reduced_trans:
  forall sys hst1 hst2 hst3,
    Reduced sys hst1 hst2 ->
    Reduced sys hst2 hst3 ->
    Reduced sys hst1 hst3.
Proof.
  unfold Reduced; intros.
  specialize (H _ _ H1); dest.
  specialize (H0 _ _ H); dest.
  split; auto.
  congruence.
Qed.

Lemma reduced_app_1:
  forall sys hfr hto,
    Reduced sys hfr hto ->
    forall hst,
      Reduced sys (hst ++ hfr) (hst ++ hto).
Proof.
  unfold Reduced; intros.
  eapply steps_split in H0; [|reflexivity]; dest.
  specialize (H _ _ H0); dest.
  split.
  - eapply steps_append; eauto.
  - red; do 2 rewrite behaviorOf_app.
    rewrite H2; reflexivity.
Qed.

Lemma reduced_app_2:
  forall sys hfr hto,
    Reduced sys hfr hto ->
    forall hst,
      Reduced sys (hfr ++ hst) (hto ++ hst).
Proof.
  unfold Reduced; intros.
  eapply steps_split in H0; [|reflexivity]; dest.
  specialize (H _ _ H1); dest.
  split.
  - eapply steps_append; eauto.
  - red; do 2 rewrite behaviorOf_app.
    rewrite H2; reflexivity.
Qed.

Lemma reduced_serializable:
  forall sys st1 hfr st2,
    steps step_m sys st1 hfr st2 ->
    forall hto,
      Reduced sys hfr hto ->
      Serializable sys hto ->
      Serializable sys hfr.
Proof.
  unfold Serializable, Reduced; intros.
  destruct H1 as [shfr [stfr [? ?]]].
  exists shfr, stfr.
  split; auto.
  specialize (H0 _ _ H); dest.
  congruence.
Qed.

Lemma reduced_to_seq_serializable:
  forall sys hst st2,
    steps step_m sys (initsOf sys) hst st2 ->
    forall shst strss,
      Reduced sys hst shst ->
      Sequential sys msg_dec shst strss ->
      Serializable sys hst.
Proof.
  intros.
  eapply reduced_serializable with (hto:= shst); eauto.
  exists shst, st2; split.
  - split; eauto.
    apply H0; auto.
  - congruence.
Qed.

(*! Reducibility of silent, incoming, and outgoing labels *)

Lemma silent_commutes_1:
  forall sys lbl,
    Reduced sys [RlblEmpty _; lbl] [lbl; RlblEmpty _].
Proof.
  unfold Reduced; intros.
  split.
  - inv H; inv H3; inv H2; inv H5.
    repeat econstructor.
    assumption.
  - inv H; inv H3; inv H2; inv H5.
    repeat econstructor.
Qed.

Lemma silent_commutes_2:
  forall sys lbl,
    Reduced sys [lbl; RlblEmpty _] [RlblEmpty _; lbl].
Proof.
  unfold Reduced; intros.
  split.
  - inv H; inv H3; inv H2; inv H6.
    repeat econstructor.
    assumption.
  - inv H; inv H3; inv H2; inv H6.
    repeat econstructor.
Qed.

Lemma silent_reduced_1:
  forall sys hst,
    Reduced sys (RlblEmpty _ :: hst) (hst ++ [RlblEmpty _]).
Proof.
  unfold Reduced; induction hst as [|lbl ?]; simpl; intros;
    [split; [auto|congruence]|].

  split.
  - change (RlblEmpty _ :: lbl :: hst) with ([RlblEmpty _; lbl] ++ hst) in H.
    eapply steps_split in H; [|reflexivity].
    destruct H as [sti [? ?]].
    eapply silent_commutes_1 in H0; dest.
    pose proof (steps_append H H0); inv H2.
    specialize (IHhst _ _ H6); dest.
    econstructor; eauto.
  - red; cbn.
    rewrite behaviorOf_app.
    simpl; rewrite app_nil_r; reflexivity.
Qed.

Lemma silent_reduced_2:
  forall sys hst,
    Reduced sys (hst ++ [RlblEmpty _]) (RlblEmpty _ :: hst).
Proof.
  unfold Reduced; induction hst as [|lbl ?]; simpl; intros;
    [split; [auto|congruence]|].

  split.
  - inv H.
    specialize (IHhst _ _ H3); dest.
    pose proof (StepsCons H _ _ H5).
    change (lbl :: RlblEmpty _ :: hst) with ([lbl; RlblEmpty _] ++ hst) in H1.
    eapply steps_split in H1; [|reflexivity].
    destruct H1 as [sti [? ?]].
    eapply silent_commutes_2 in H2; dest.
    pose proof (steps_append H1 H2); auto.
  - red; cbn.
    rewrite behaviorOf_app.
    simpl; rewrite app_nil_r; reflexivity.
Qed.

Lemma msg_ins_commutes_1:
  forall sys eins lbl,
    Internal lbl ->
    Reduced sys [RlblIns eins; lbl] [lbl; RlblIns eins].
Proof.
  unfold Reduced; intros.
  split.
  - destruct lbl as [| |hdl mins mouts|]; [elim H|elim H| |elim H].
    dest_step_m.
    econstructor.
    + econstructor.
      * econstructor. 
      * econstructor; eauto. 
    + econstructor; try reflexivity; try eassumption.
      * eapply FirstMPI_Forall_enqMsgs; eauto. 
      * f_equal.
        rewrite enqMsgs_enqMsgs_comm.
        { rewrite enqMsgs_deqMsgs_FirstMPI_comm; auto.
          destruct H10; auto.
        }
        { destruct H2, H17.
          eapply DisjList_SubList; eauto.
          eapply DisjList_comm, DisjList_SubList; eauto.
          apply DisjList_app_4.
          { apply mindsOf_merqsOf_DisjList. }
          { apply DisjList_comm, merqsOf_merssOf_DisjList. }
        }
  - hnf; cbn.
    destruct lbl; [elim H|elim H|auto|elim H].
Qed.

Lemma msg_ins_reduced_1:
  forall sys eins hst,
    InternalHistory hst ->
    Reduced sys (RlblIns eins :: hst) (hst ++ [RlblIns eins]).
Proof.
  unfold Reduced; induction hst as [|lbl ?]; simpl; intros;
    [split; [assumption|reflexivity]|].
  inv H.
  split.
  - change (RlblIns eins :: lbl :: hst) with ([RlblIns eins; lbl] ++ hst) in H0.
    eapply steps_split in H0; [|reflexivity].
    destruct H0 as [sti [? ?]].
    eapply msg_ins_commutes_1 in H0; [|assumption]; dest.
    pose proof (steps_append H H0); inv H2.
    specialize (IHhst H4 _ _ H8); dest.
    econstructor; eauto.
  - red; cbn.
    rewrite behaviorOf_app.
    rewrite internal_history_behavior_nil by assumption.
    destruct lbl; auto; elim H3.
Qed.

Lemma msg_ins_reduced_2:
  forall sys hst inits ins outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
    forall eins,
      DisjList ins eins ->
      Reduced sys (hst ++ [RlblIns eins]) (RlblIns eins :: hst).
Proof.
Admitted.

Lemma msg_outs_commutes_1:
  forall sys eouts lbl,
    Internal lbl ->
    Reduced sys [lbl; RlblOuts eouts] [RlblOuts eouts; lbl].
Proof.
  unfold Reduced; intros.
  split.
  - destruct lbl as [| |hdl mins mouts|]; [elim H|elim H| |elim H].
    dest_step_m.
    econstructor.
      + econstructor.
        * econstructor.
        * econstructor; try reflexivity; try eassumption.
          assert (DisjList (idsOf mins) (idsOf eouts)).
          { destruct H3, H12.
            eapply DisjList_SubList; eauto.
            eapply DisjList_comm, DisjList_SubList; eauto.
            apply DisjList_comm, mindsOf_merssOf_DisjList.
          }
          eapply FirstMPI_Forall_deqMsgs; eauto.
      + assert (DisjList (idsOf eouts) (idsOf mins)).
        { destruct H3, H12.
          eapply DisjList_SubList; eauto.
          eapply DisjList_comm, DisjList_SubList; eauto.
          apply mindsOf_merssOf_DisjList.
        }
        econstructor; try reflexivity; try eassumption.
        * eapply FirstMPI_Forall_enqMsgs.
          rewrite <-FirstMPI_Forall_deqMsgs; eauto.
        * f_equal; rewrite <-enqMsgs_deqMsgs_FirstMPI_comm.
          { f_equal; eapply deqMsgs_deqMsgs_comm.
            apply DisjList_comm; auto.
          }
          { destruct H3; auto. }
          { rewrite <-FirstMPI_Forall_deqMsgs; eauto. }
  - hnf; cbn.
    destruct lbl; [elim H|elim H|auto|elim H].
Qed.

Lemma msg_outs_reduced_1:
  forall sys eouts hst,
    InternalHistory hst ->
    Reduced sys (hst ++ [RlblOuts eouts]) (RlblOuts eouts :: hst).
Proof.
  unfold Reduced; induction hst as [|lbl ?]; simpl; intros; 
    [split; [assumption|reflexivity]|].
  inv H0; inv H.
  split.
  - specialize (IHhst H3 _ _ H4); dest.
    assert (steps step_m sys st1 (lbl :: RlblOuts eouts :: hst) st2)
      by (econstructor; eauto).
    change (lbl :: RlblOuts eouts :: hst) with
        ([lbl; RlblOuts eouts] ++ hst) in H1.
    eapply steps_split in H1; [|reflexivity].
    destruct H1 as [sti [? ?]].
    change (RlblOuts eouts :: lbl :: hst) with
        ([RlblOuts eouts; lbl] ++ hst).
    eapply steps_append; eauto.
    eapply msg_outs_commutes_1; eauto.
  - red; cbn.
    rewrite behaviorOf_app.
    rewrite internal_history_behavior_nil by assumption.
    destruct lbl; auto; elim H2.
Qed.

(** FIXME: need more conditions *)
Lemma msg_outs_reduced_2:
  forall sys hst inits ins outs eouts mouts,
    Atomic msg_dec inits ins hst outs eouts ->
    Reduced sys (RlblOuts mouts :: hst) (hst ++ [RlblOuts mouts]).
Proof.
Admitted.

(*! Reducibility of internal state transitions *)

Lemma msg_int_commutes_1:
  forall sys rule1 ins1 outs1 rule2 ins2 outs2,
    rule_oidx rule1 <> rule_oidx rule2 ->
    DisjList (idsOf ins1) (idsOf ins2) ->
    DisjList (idsOf outs1) (idsOf ins2) ->
    DisjList (idsOf outs1) (idsOf outs2) ->
    Reduced sys [RlblInt rule2 ins2 outs2; RlblInt rule1 ins1 outs1]
            [RlblInt rule1 ins1 outs1; RlblInt rule2 ins2 outs2].
Proof.
  unfold Reduced; intros.
  split; [|reflexivity].
  dest_step_m.
  econstructor.
  - econstructor.
    + econstructor.
    + econstructor; try reflexivity; try eassumption.
      * mred.
      * mred.
      * eapply FirstMPI_Forall_enqMsgs_inv in H22;
          [|apply DisjList_comm; auto].
        eapply FirstMPI_Forall_deqMsgs; eauto.
        apply DisjList_comm; auto.
  - econstructor; try reflexivity; try eassumption.
    + mred.
    + mred.
    + apply FirstMPI_Forall_enqMsgs.
      apply FirstMPI_Forall_deqMsgs; auto.
    + f_equal.
      * meq.
      * meq.
      * rewrite <-enqMsgs_deqMsgs_comm with (minds1:= idsOf ins2)
          by (apply DisjList_comm; assumption).
        rewrite deqMsgs_deqMsgs_comm by (apply DisjList_comm; assumption).
        rewrite enqMsgs_enqMsgs_comm with (msgs1:= outs2)
          by (apply DisjList_comm; assumption).
        rewrite enqMsgs_deqMsgs_FirstMPI_comm with (msgs2:= outs2).
        { reflexivity. }
        { destruct H13; auto. }
        { apply FirstMPI_Forall_deqMsgs; auto. }
Qed.

