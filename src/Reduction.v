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

Definition Reducible (sys: System) (hfr hto: MHistory) :=
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
  forall hst,
    InternalHistory hst -> behaviorOf hst = nil.
Proof.
  induction hst; simpl; intros; auto.
  inv H; rewrite IHhst by assumption.
  destruct a; auto; elim H2.
Qed.

Lemma reducible_refl:
  forall sys hst, Reducible sys hst hst.
Proof.
  unfold Reducible; intros.
  split; auto.
  congruence.
Qed.

Lemma reducible_trans:
  forall sys hst1 hst2 hst3,
    Reducible sys hst1 hst2 ->
    Reducible sys hst2 hst3 ->
    Reducible sys hst1 hst3.
Proof.
  unfold Reducible; intros.
  specialize (H _ _ H1); dest.
  specialize (H0 _ _ H); dest.
  split; auto.
  congruence.
Qed.

Lemma reducible_app_1:
  forall sys hfr hto,
    Reducible sys hfr hto ->
    forall hst,
      Reducible sys (hst ++ hfr) (hst ++ hto).
Proof.
  unfold Reducible; intros.
  eapply steps_split in H0; [|reflexivity]; dest.
  specialize (H _ _ H0); dest.
  split.
  - eapply steps_append; eauto.
  - apply bequivalent_app_1; auto.
Qed.

Lemma reducible_app_2:
  forall sys hfr hto,
    Reducible sys hfr hto ->
    forall hst,
      Reducible sys (hfr ++ hst) (hto ++ hst).
Proof.
  unfold Reducible; intros.
  eapply steps_split in H0; [|reflexivity]; dest.
  specialize (H _ _ H1); dest.
  split.
  - eapply steps_append; eauto.
  - apply bequivalent_app_2; auto.
Qed.

Corollary reducible_cons:
  forall sys hfr hto,
    Reducible sys hfr hto ->
    forall lbl,
      Reducible sys (lbl :: hfr) (lbl :: hto).
Proof.
  intros.
  change (lbl :: hfr) with ([lbl] ++ hfr).
  change (lbl :: hto) with ([lbl] ++ hto).
  apply reducible_app_1; auto.
Qed.

Corollary reducible_cons_2:
  forall sys lbl1 lbl2 lbl3 lbl4,
    Reducible sys [lbl1; lbl2] [lbl3; lbl4] ->
    forall hst,
      Reducible sys (lbl1 :: lbl2 :: hst) (lbl3 :: lbl4 :: hst).
Proof.
  intros.
  change (lbl1 :: lbl2 :: hst) with ([lbl1; lbl2] ++ hst).
  change (lbl3 :: lbl4 :: hst) with ([lbl3; lbl4] ++ hst).
  apply reducible_app_2; auto.
Qed.

Lemma reducible_serializable:
  forall sys st1 hfr st2,
    steps step_m sys st1 hfr st2 ->
    forall hto,
      steps step_m sys st1 hto st2 ->
      BEquivalent sys hfr hto ->
      (* Reducible sys hfr hto -> *)
      Serializable sys hto ->
      Serializable sys hfr.
Proof.
  unfold Serializable, Reducible; intros.
  destruct H2 as [shfr [stfr [? ?]]].
  exists shfr, stfr.
  split; auto.
  eapply bequivalent_trans; eauto.
Qed.

(*! Reducibility of silent, incoming, and outgoing labels *)

Lemma silent_commutes_1:
  forall sys lbl,
    Reducible sys [RlblEmpty _; lbl] [lbl; RlblEmpty _].
Proof.
  unfold Reducible; intros.
  split.
  - inv H; inv H3; inv H2; inv H5.
    repeat econstructor.
    assumption.
  - inv H; inv H3; inv H2; inv H5.
    repeat econstructor.
Qed.

Lemma silent_commutes_2:
  forall sys lbl,
    Reducible sys [lbl; RlblEmpty _] [RlblEmpty _; lbl].
Proof.
  unfold Reducible; intros.
  split.
  - inv H; inv H3; inv H2; inv H6.
    repeat econstructor.
    assumption.
  - inv H; inv H3; inv H2; inv H6.
    repeat econstructor.
Qed.

Lemma silent_reducible_1:
  forall sys hst,
    Reducible sys (RlblEmpty _ :: hst) (hst ++ [RlblEmpty _]).
Proof.
  unfold Reducible; induction hst as [|lbl ?]; simpl; intros;
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

Lemma silent_reducible_2:
  forall sys hst,
    Reducible sys (hst ++ [RlblEmpty _]) (RlblEmpty _ :: hst).
Proof.
  unfold Reducible; induction hst as [|lbl ?]; simpl; intros;
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
    InternalLbl lbl ->
    Reducible sys [RlblIns eins; lbl] [lbl; RlblIns eins].
Proof.
  unfold Reducible; intros.
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
          destruct H12; auto.
        }
        { destruct H2, H18.
          eapply DisjList_SubList; eauto.
          eapply DisjList_comm, DisjList_SubList; eauto.
          apply DisjList_app_4.
          { apply sys_minds_sys_merqs_DisjList. }
          { apply DisjList_comm, sys_merqs_sys_merss_DisjList. }
        }
  - hnf; cbn.
    destruct lbl; [elim H|elim H|auto|elim H].
Qed.

Lemma msg_ins_commutes_2:
  forall sys eins oidx ridx ins outs,
    DisjList eins ins ->
    DisjList (idsOf eins) (idsOf outs) ->
    Reducible sys [RlblInt oidx ridx ins outs; RlblIns eins]
              [RlblIns eins; RlblInt oidx ridx ins outs].
Proof.
  unfold Reducible; intros.
  split.
  - dest_step_m.
    econstructor.
    + econstructor.
      * econstructor.
      * econstructor; try reflexivity; try eassumption.
        eapply FirstMPI_Forall_enqMsgs_inv; [|eassumption].
        apply DisjList_comm; auto.
    + econstructor; try reflexivity; try eassumption.
      f_equal.
      rewrite <-enqMsgs_deqMsgs_FirstMPI_comm.
      * rewrite enqMsgs_enqMsgs_comm; [reflexivity|].
        apply DisjList_comm; auto.
      * destruct H14; auto.
      * eapply FirstMPI_Forall_enqMsgs_inv; [|eassumption].
        apply DisjList_comm; auto.
  - hnf; cbn; reflexivity.
Qed.

Lemma msg_ins_reducible_1:
  forall sys eins hst,
    InternalHistory hst ->
    Reducible sys (RlblIns eins :: hst) (hst ++ [RlblIns eins]).
Proof.
  unfold Reducible; induction hst as [|lbl ?]; simpl; intros;
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

Lemma msg_ins_reducible_2:
  forall sys hst inits ins outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
    forall eins,
      DisjList eins ins ->
      DisjList (idsOf eins) (idsOf outs) ->
      Reducible sys (hst ++ [RlblIns eins]) (RlblIns eins :: hst).
Proof.
  induction 1; simpl; intros;
    [apply msg_ins_commutes_2; auto|].

  subst.
  apply DisjList_comm, DisjList_app_3 in H5; dest.
  apply DisjList_comm in H2; apply DisjList_comm in H3.
  rewrite idsOf_app in H6.
  apply DisjList_comm, DisjList_app_3 in H6; dest.
  apply DisjList_comm in H4; apply DisjList_comm in H5.
  specialize (IHAtomic _ H2 H4).

  eapply reducible_trans.
  - apply reducible_cons; eassumption.
  - apply reducible_cons_2.
    apply msg_ins_commutes_2; auto.
Qed.

Lemma msg_outs_commutes_1:
  forall sys eouts oidx ridx ins outs,
    DisjList eouts outs ->
    DisjList (idsOf eouts) (idsOf ins) ->
    Reducible sys [RlblOuts eouts; RlblInt oidx ridx ins outs]
              [RlblInt oidx ridx ins outs; RlblOuts eouts].
Proof.
  unfold Reducible; intros.
  split.
  - dest_step_m.
    econstructor.
    + econstructor.
      * econstructor.
      * econstructor; try reflexivity; try eassumption.
        apply FirstMPI_Forall_enqMsgs_inv in H3; [|assumption].
        apply FirstMPI_Forall_deqMsgs in H3; auto.
    + econstructor; try reflexivity; try eassumption.
      * apply FirstMPI_Forall_deqMsgs; auto.
        apply DisjList_comm; auto.
      * f_equal.
        rewrite <-enqMsgs_deqMsgs_FirstMPI_comm.
        { rewrite deqMsgs_deqMsgs_comm; auto. }
        { destruct H4; auto. }
        { apply FirstMPI_Forall_enqMsgs_inv in H3; assumption. }
  - hnf; cbn; reflexivity.
Qed.

Lemma msg_outs_commutes_2:
  forall sys eouts lbl,
    InternalLbl lbl ->
    Reducible sys [lbl; RlblOuts eouts] [RlblOuts eouts; lbl].
Proof.
  unfold Reducible; intros.
  split.
  - destruct lbl as [| |oidx ridx mins mouts|]; [elim H|elim H| |elim H].
    dest_step_m.
    econstructor.
    + econstructor.
      * econstructor.
      * econstructor; try reflexivity; try eassumption.
        assert (DisjList (idsOf mins) (idsOf eouts)).
        { destruct H3, H14.
          eapply DisjList_SubList; eauto.
          eapply DisjList_comm, DisjList_SubList; eauto.
          apply DisjList_comm, sys_minds_sys_merss_DisjList.
        }
        eapply FirstMPI_Forall_deqMsgs; eauto.
    + assert (DisjList (idsOf eouts) (idsOf mins)).
      { destruct H3, H14.
        eapply DisjList_SubList; eauto.
        eapply DisjList_comm, DisjList_SubList; eauto.
        apply sys_minds_sys_merss_DisjList.
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

Lemma msg_outs_reducible_1:
  forall sys hst inits ins outs eouts mouts,
    DisjList (idsOf mouts) (idsOf ins) ->
    DisjList mouts outs ->
    Atomic msg_dec inits ins hst outs eouts ->
    Reducible sys (RlblOuts mouts :: hst) (hst ++ [RlblOuts mouts]).
Proof.
  induction 3; simpl; intros;
    [apply msg_outs_commutes_1; auto|].

  subst.
  apply DisjList_comm, DisjList_app_3 in H0; dest.
  apply DisjList_comm in H0; apply DisjList_comm in H4.
  rewrite idsOf_app in H.
  apply DisjList_comm, DisjList_app_3 in H; dest.
  apply DisjList_comm in H; apply DisjList_comm in H5.
  specialize (IHAtomic H H0).

  eapply reducible_trans; [|apply reducible_cons; eassumption].
  apply reducible_cons_2.
  apply msg_outs_commutes_1; auto.
Qed.

Lemma msg_outs_reducible_2:
  forall sys eouts hst,
    InternalHistory hst ->
    Reducible sys (hst ++ [RlblOuts eouts]) (RlblOuts eouts :: hst).
Proof.
  unfold Reducible; induction hst as [|lbl ?]; simpl; intros; 
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
    eapply msg_outs_commutes_2; eauto.
  - red; cbn.
    rewrite behaviorOf_app.
    rewrite internal_history_behavior_nil by assumption.
    destruct lbl; auto; elim H2.
Qed.

(*! Reducibility of internal state transitions *)

Lemma msg_int_commutes:
  forall sys oidx1 ridx1 ins1 outs1 oidx2 ridx2 ins2 outs2,
    oidx1 <> oidx2 ->
    DisjList (idsOf ins1) (idsOf ins2) ->
    DisjList (idsOf outs1) (idsOf ins2) ->
    DisjList (idsOf outs1) (idsOf outs2) ->
    Reducible sys [RlblInt oidx2 ridx2 ins2 outs2; RlblInt oidx1 ridx1 ins1 outs1]
              [RlblInt oidx1 ridx1 ins1 outs1; RlblInt oidx2 ridx2 ins2 outs2].
Proof.
  unfold Reducible; intros.
  split; [|reflexivity].
  dest_step_m.
  econstructor.
  - econstructor.
    + econstructor.
    + econstructor; try reflexivity; try eassumption.
      * mred.
      * mred.
      * eapply FirstMPI_Forall_enqMsgs_inv in H25.
        { eapply FirstMPI_Forall_deqMsgs; [|eassumption].
          apply DisjList_comm; auto.
        }
        { apply DisjList_comm, idsOf_DisjList; auto. }
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
        { destruct H15; auto. }
        { apply FirstMPI_Forall_deqMsgs; auto. }
Qed.

