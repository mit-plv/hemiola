Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM SemFacts.
Require Import Topology Serial SerialFacts.

Set Implicit Arguments.

Open Scope list.

Ltac dest_steps :=
  repeat match goal with
         | [H: steps step_m _ _ _ _ |- _] => inv H
         end; simpl in *.

Ltac dest_step_m :=
  repeat match goal with
         | [H: step_m _ _ _ _ |- _] => inv H
         | [H: {| bst_oss := _ |} = {| bst_oss := _ |} |- _] => inv H
         end; simpl in *.

Definition Reducible (sys: System) (hfr hto: MHistory) :=
  forall st1 st2,
    steps step_m sys st1 hfr st2 ->
    steps step_m sys st1 hto st2.

(*! General Facts *)

Definition InternalLbl (lbl: MLabel) :=
  match lbl with
  | RlblInt _ _ _ _ => True
  | _ => False
  end.

Definition InsLbl (lbl: MLabel) :=
  match lbl with
  | RlblIns _ => True
  | _ => False
  end.

Definition OutsLbl (lbl: MLabel) :=
  match lbl with
  | RlblOuts _ => True
  | _ => False
  end.

Definition NonInsLbl (lbl: MLabel) :=
  match lbl with
  | RlblIns _ => False
  | _ => True
  end.

Definition NonOutsLbl (lbl: MLabel) :=
  match lbl with
  | RlblOuts _ => False
  | _ => True
  end.

Definition HistoryP (P: MLabel -> Prop) (hst: MHistory) :=
  Forall (fun lbl => P lbl) hst.

Definition InternalHistory := HistoryP InternalLbl.
Definition InsHistory := HistoryP InsLbl.
Definition OutsHistory := HistoryP OutsLbl.
Definition NonInsHistory := HistoryP NonInsLbl.
Definition NonOutsHistory := HistoryP NonOutsLbl.

Lemma atomic_internal_history:
  forall inits ins hst outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
    InternalHistory hst.
Proof.
  induction 1; simpl; intros.
  - repeat constructor.
  - repeat constructor; auto.
Qed.

(* Lemma internal_history_behaviorIO_nil: *)
(*   forall hst, *)
(*     InternalHistory hst -> *)
(*     behaviorIO hst = (nil, nil). *)
(* Proof. *)
(*   induction hst; simpl; intros; auto. *)
(*   inv H; specialize (IHhst H3). *)
(*   unfold behaviorIO in *. *)
(*   destruct a; simpl; auto; elim H2. *)
(* Qed. *)

Lemma reducible_refl:
  forall sys hst, Reducible sys hst hst.
Proof.
  congruence.
Qed.

Lemma reducible_trans:
  forall sys hst1 hst2 hst3,
    Reducible sys hst1 hst2 ->
    Reducible sys hst2 hst3 ->
    Reducible sys hst1 hst3.
Proof.
  unfold Reducible; intros; auto.
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
  eapply steps_append; eauto.
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
  eapply steps_append; eauto.
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
      Serializable sys hto st2 ->
      Serializable sys hfr st2.
Proof.
  intros; auto.
Qed.

(*! Reducibility of silent, incoming, and outgoing labels *)

Lemma silent_ignored_1:
  forall sys hst,
    Reducible sys (RlblEmpty _ :: hst) hst.
Proof.
  unfold Reducible; intros.
  inv H; inv H5; assumption.
Qed.

Lemma silent_ignored_2:
  forall sys hst,
    Reducible sys (hst ++ [RlblEmpty _]) hst.
Proof.
  unfold Reducible; intros.
  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  inv H; inv H4; inv H6.
  assumption.
Qed.

Lemma silent_commutes_1:
  forall sys lbl,
    Reducible sys [RlblEmpty _; lbl] [lbl; RlblEmpty _].
Proof.
  unfold Reducible; intros.
  inv H; inv H3; inv H2; inv H5.
  repeat econstructor; assumption.
Qed.

Lemma silent_commutes_2:
  forall sys lbl,
    Reducible sys [lbl; RlblEmpty _] [RlblEmpty _; lbl].
Proof.
  unfold Reducible; intros.
  inv H; inv H3; inv H2; inv H6.
  repeat econstructor; assumption.
Qed.

Lemma silent_reducible_1:
  forall sys hst,
    Reducible sys (RlblEmpty _ :: hst) (hst ++ [RlblEmpty _]).
Proof.
  unfold Reducible; induction hst as [|lbl ?]; simpl; intros; auto.

  change (RlblEmpty _ :: lbl :: hst) with ([RlblEmpty _; lbl] ++ hst) in H.
  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  eapply silent_commutes_1 in H0; dest.
  pose proof (steps_append H H0); inv H1.
  specialize (IHhst _ _ H5); dest.
  econstructor; eauto.
Qed.

Lemma silent_reducible_2:
  forall sys hst,
    Reducible sys (hst ++ [RlblEmpty _]) (RlblEmpty _ :: hst).
Proof.
  unfold Reducible; induction hst as [|lbl ?]; simpl; intros; auto.

  inv H.
  specialize (IHhst _ _ H3).
  pose proof (StepsCons IHhst _ _ H5).
  change (lbl :: RlblEmpty _ :: hst) with ([lbl; RlblEmpty _] ++ hst) in H.
  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  eapply silent_commutes_2 in H0; dest.
  pose proof (steps_append H H0); auto.
Qed.

Lemma outs_ins_commutes:
  forall sys eins eouts,
    Reducible sys [RlblIns eins; RlblOuts eouts] [RlblOuts eouts; RlblIns eins].
Proof.
  unfold Reducible; intros.
  dest_steps; dest_step_m.
  econstructor.
  - econstructor.
    + econstructor.
    + econstructor; eauto.
  - econstructor; try reflexivity; try eassumption.
    + eapply FirstMPI_Forall_enqMsgs; eauto. 
    + f_equal.
      rewrite enqMsgs_deqMsgs_FirstMPI_comm; auto.
      destruct H2; auto.
Qed.

Lemma int_ins_commutes:
  forall sys eins oidx ridx ins outs,
    Reducible sys [RlblIns eins; RlblInt oidx ridx ins outs]
              [RlblInt oidx ridx ins outs; RlblIns eins].
Proof.
  unfold Reducible; intros.
  dest_steps; dest_step_m.
  econstructor.
  - econstructor.
    + econstructor.
    + econstructor; eauto.
  - econstructor; try reflexivity; try eassumption.
    + eapply FirstMPI_Forall_enqMsgs; eauto. 
    + f_equal.
      rewrite enqMsgs_enqMsgs_comm.
      { rewrite enqMsgs_deqMsgs_FirstMPI_comm; auto.
        destruct H11; auto.
      }
      { destruct H1, H17.
        eapply DisjList_SubList; eauto.
        eapply DisjList_comm, DisjList_SubList; eauto.
        apply DisjList_app_4.
        { apply sys_minds_sys_merqs_DisjList. }
        { apply DisjList_comm, sys_merqs_sys_merss_DisjList. }
      }      
Qed.

Lemma ins_commutes:
  forall sys eins lbl,
    NonInsLbl lbl ->
    Reducible sys [RlblIns eins; lbl] [lbl; RlblIns eins].
Proof.
  intros.
  destruct lbl; [|elim H| |].
  - apply silent_commutes_2.
  - apply int_ins_commutes.
  - apply outs_ins_commutes.
Qed.

Lemma ins_reducible:
  forall sys eins hst,
    NonInsHistory hst ->
    Reducible sys (RlblIns eins :: hst) (hst ++ [RlblIns eins]).
Proof.
  unfold Reducible; induction hst as [|lbl ?]; simpl; intros; auto.
  inv H.
  change (RlblIns eins :: lbl :: hst) with ([RlblIns eins; lbl] ++ hst) in H0.
  eapply steps_split in H0; [|reflexivity].
  destruct H0 as [sti [? ?]].
  eapply ins_commutes in H0; [|assumption]; dest.
  pose proof (steps_append H H0); inv H1.
  specialize (IHhst H4 _ _ H7); dest.
  econstructor; eauto.
Qed.

Lemma outs_int_commutes:
  forall sys oidx ridx ins outs eouts,
    Reducible sys [RlblInt oidx ridx ins outs; RlblOuts eouts]
              [RlblOuts eouts; RlblInt oidx ridx ins outs].
Proof.
  unfold Reducible; intros.
  dest_steps; dest_step_m.
  econstructor.
  - econstructor.
    + econstructor.
    + econstructor; try reflexivity; try eassumption.
      assert (DisjList (idsOf ins) (idsOf eouts)).
      { destruct H2, H13.
        eapply DisjList_SubList; eauto.
        eapply DisjList_comm, DisjList_SubList; eauto.
        apply DisjList_comm, sys_minds_sys_merss_DisjList.
      }
      eapply FirstMPI_Forall_deqMsgs; eauto.
  - assert (DisjList (idsOf eouts) (idsOf ins)).
    { destruct H2, H13.
      eapply DisjList_SubList; eauto.
      eapply DisjList_comm, DisjList_SubList; eauto.
      apply sys_minds_sys_merss_DisjList.
    }
    econstructor; try reflexivity; try eassumption.
    + eapply FirstMPI_Forall_enqMsgs.
      rewrite <-FirstMPI_Forall_deqMsgs; eauto.
    + f_equal; rewrite <-enqMsgs_deqMsgs_FirstMPI_comm.
      * f_equal; eapply deqMsgs_deqMsgs_comm.
        apply DisjList_comm; auto.
      * destruct H2; auto.
      * rewrite <-FirstMPI_Forall_deqMsgs; eauto.
Qed.

Lemma outs_commutes:
  forall sys eouts lbl,
    NonOutsLbl lbl ->
    Reducible sys [lbl; RlblOuts eouts] [RlblOuts eouts; lbl].
Proof.
  intros.
  destruct lbl; [| | |elim H].
  - apply silent_commutes_1.
  - apply outs_ins_commutes.
  - apply outs_int_commutes.
Qed.

Lemma outs_reducible:
  forall sys eouts hst,
    NonOutsHistory hst ->
    Reducible sys (hst ++ [RlblOuts eouts]) (RlblOuts eouts :: hst).
Proof.
  unfold Reducible; induction hst as [|lbl ?]; simpl; intros; auto.
  inv H0; inv H.
  specialize (IHhst H3 _ _ H4); dest.
  assert (steps step_m sys st1 (lbl :: RlblOuts eouts :: hst) st2)
    by (econstructor; eauto).
  change (lbl :: RlblOuts eouts :: hst) with
      ([lbl; RlblOuts eouts] ++ hst) in H.
  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  change (RlblOuts eouts :: lbl :: hst) with
      ([RlblOuts eouts; lbl] ++ hst).
  eapply steps_append; eauto.
  eapply outs_commutes; eauto.
Qed.

(*! Reducing a history to (Ins -> Internals -> Outs) *)

Theorem hst_reducible_to_ins_ints_outs:
  forall sys hst,
  exists ins ints outs,
    InsHistory ins /\
    InternalHistory ints /\
    OutsHistory outs /\
    Reducible sys hst (outs ++ ints ++ ins).
Proof.
  induction hst as [|lbl hst]; simpl; intros.
  - exists nil, nil, nil.
    repeat split; try constructor.
    simpl; red; intros; assumption.
  - destruct IHhst as [ins [ints [outs ?]]]; dest.
    destruct lbl.
    + exists ins, ints, outs.
      repeat split; auto.
      eapply reducible_trans; [|eassumption].
      apply silent_ignored_1.
    + exists (RlblIns mins :: ins), ints, outs.
      repeat split; auto.
      * constructor; simpl; auto.
      * change (RlblIns mins :: hst) with ([RlblIns mins] ++ hst).
        eapply reducible_trans.
        { eapply reducible_app_1; eassumption. }
        { change (outs ++ ints ++ RlblIns mins :: ins)
            with (outs ++ ints ++ [RlblIns mins] ++ ins).
          repeat rewrite app_assoc.
          apply reducible_app_2.
          rewrite <-app_assoc with (n:= ints).
          apply ins_reducible.
          apply Forall_app.
          { eapply Forall_impl with (P:= OutsLbl); auto.
            intros; destruct a; intuition.
          }
          { eapply Forall_impl with (P:= InternalLbl); auto.
            intros; destruct a; intuition.
          }
        }
    + exists ins, (RlblInt oidx ridx mins mouts :: ints), outs.
      repeat split; auto.
      * constructor; simpl; auto.
      * change (RlblInt oidx ridx mins mouts :: hst)
          with ([RlblInt oidx ridx mins mouts] ++ hst).
        eapply reducible_trans.
        { eapply reducible_app_1; eassumption. }
        { change (outs ++ (RlblInt oidx ridx mins mouts :: ints) ++ ins)
            with (outs ++ [RlblInt oidx ridx mins mouts] ++ ints ++ ins).
          repeat rewrite app_assoc.
          do 2 apply reducible_app_2.
          clear -H1.
          induction outs; simpl; [apply reducible_refl|].
          inv H1.
          destruct a as [| | |eouts]; try (intuition; fail).
          eapply reducible_trans.
          { change (RlblInt oidx ridx mins mouts :: RlblOuts eouts :: outs)
              with ([RlblInt oidx ridx mins mouts; RlblOuts eouts] ++ outs).
            eapply reducible_app_2.
            eapply outs_int_commutes.
          }
          { apply reducible_cons; auto. }
        }
    + exists ins, ints, (RlblOuts mouts :: outs).
      repeat split; auto.
      * constructor; simpl; auto.
      * change (RlblOuts mouts :: hst) with ([RlblOuts mouts] ++ hst).
        eapply reducible_trans.
        { eapply reducible_app_1; eassumption. }
        { apply reducible_refl. }
Qed.
  
(* NOTE: For the reducibility of internal state transitions, see [Commutable.v]. *)

Close Scope list.

