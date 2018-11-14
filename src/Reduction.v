Require Import Bool List String Peano_dec Omega.
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

Definition Reducible {oifc} (sys: System oifc) (hfr hto: MHistory) :=
  forall st1 st2,
    steps step_m sys st1 hfr st2 ->
    steps step_m sys st1 hto st2.

(*! General Facts *)

Lemma reducible_refl:
  forall {oifc} (sys: System oifc) hst, Reducible sys hst hst.
Proof.
  congruence.
Qed.

Lemma reducible_trans:
  forall {oifc} (sys: System oifc) hst1 hst2 hst3,
    Reducible sys hst1 hst2 ->
    Reducible sys hst2 hst3 ->
    Reducible sys hst1 hst3.
Proof.
  unfold Reducible; intros; auto.
Qed.

Lemma reducible_app_1:
  forall {oifc} (sys: System oifc) hfr hto,
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
  forall {oifc} (sys: System oifc) hfr hto,
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
  forall {oifc} (sys: System oifc) hfr hto,
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
  forall {oifc} (sys: System oifc) lbl1 lbl2 lbl3 lbl4,
    Reducible sys [lbl1; lbl2] [lbl3; lbl4] ->
    forall hst,
      Reducible sys (lbl1 :: lbl2 :: hst) (lbl3 :: lbl4 :: hst).
Proof.
  intros.
  change (lbl1 :: lbl2 :: hst) with ([lbl1; lbl2] ++ hst).
  change (lbl3 :: lbl4 :: hst) with ([lbl3; lbl4] ++ hst).
  apply reducible_app_2; auto.
Qed.

(* Lemma reducible_app_rev_1: *)
(*   forall sys hfr hto hst, *)
(*     Reducible sys (hst ++ hfr) (hst ++ hto) -> *)
(*     Reducible sys hfr hto. *)
(* Proof. *)
(*   unfold Reducible; intros. *)
  
Lemma reducible_serializable:
  forall {oifc} (sys: System oifc) st1 hfr st2,
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
  forall {oifc} (sys: System oifc) hst,
    Reducible sys (RlblEmpty _ :: hst) hst.
Proof.
  unfold Reducible; intros.
  inv H; inv H5; assumption.
Qed.

Lemma silent_ignored_2:
  forall {oifc} (sys: System oifc) hst,
    Reducible sys (hst ++ [RlblEmpty _]) hst.
Proof.
  unfold Reducible; intros.
  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  inv H; inv H4; inv H6.
  assumption.
Qed.

Lemma silent_commutes_1:
  forall {oifc} (sys: System oifc) lbl,
    Reducible sys [RlblEmpty _; lbl] [lbl; RlblEmpty _].
Proof.
  unfold Reducible; intros.
  inv H; inv H3; inv H2; inv H5.
  repeat econstructor; assumption.
Qed.

Lemma silent_commutes_2:
  forall {oifc} (sys: System oifc) lbl,
    Reducible sys [lbl; RlblEmpty _] [RlblEmpty _; lbl].
Proof.
  unfold Reducible; intros.
  inv H; inv H3; inv H2; inv H6.
  repeat econstructor; assumption.
Qed.

Lemma silent_reducible_1:
  forall {oifc} (sys: System oifc) hst,
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
  forall {oifc} (sys: System oifc) hst,
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
  forall {oifc} (sys: System oifc) eins eouts,
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
  forall {oifc} (sys: System oifc) eins oidx ridx ins outs,
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
  forall {oifc} (sys: System oifc) eins lbl,
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
  forall {oifc} (sys: System oifc) eins hst,
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
  forall {oifc} (sys: System oifc) oidx ridx ins outs eouts,
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
  forall {oifc} (sys: System oifc) eouts lbl,
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
  forall {oifc} (sys: System oifc) eouts hst,
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

Theorem trss_reducible_to_ins_atomics_outs:
  forall {oifc} (sys: System oifc) trss,
    Forall (STransactional msg_dec) trss ->
    exists ins atms outs,
      InsHistory ins /\
      Forall (AtomicEx msg_dec) atms /\
      OutsHistory outs /\
      Reducible sys (List.concat trss) (outs ++ List.concat atms ++ ins) /\
      List.length outs + List.length atms + List.length ins <= List.length trss.
Proof.
  induction trss as [|trs trss]; simpl; intros.

  - exists nil, nil, nil.
    repeat split; try constructor.
    simpl; red; intros; assumption.

  - inv H; specialize (IHtrss H3).
    destruct IHtrss as [ins [atms [outs ?]]]; dest.
    destruct H2; subst.
    + exists ins, atms, outs.
      repeat split; auto.
      eapply reducible_trans; [|eassumption].
      apply silent_ignored_1.
    + exists (RlblIns eins :: ins), atms, outs.
      repeat split; auto.
      * constructor; simpl; auto.
      * eapply reducible_trans.
        { eapply reducible_app_1; eassumption. }
        { change (outs ++ List.concat atms ++ RlblIns eins :: ins)
            with (outs ++ List.concat atms ++ [RlblIns eins] ++ ins).
          repeat rewrite app_assoc.
          apply reducible_app_2.
          rewrite <-app_assoc with (n:= List.concat atms).
          apply ins_reducible.
          apply Forall_app.
          { eapply Forall_impl with (P:= @OutsLbl _); auto.
            intros; destruct a; intuition.
          }
          { eapply Forall_impl with (Q:= @InternalHistory _) in H0;
              [|apply atomicEx_internal_history].
            clear -H0.
            induction atms; simpl; auto.
            inv H0; apply Forall_app; auto.
            apply Forall_impl with (P:= @InternalLbl _); auto.
            intros; destruct a0; intuition.
          }
        }
      * simpl; omega.
    + exists ins, atms, (RlblOuts eouts :: outs).
      repeat split; auto.
      * constructor; simpl; auto.
      * eapply reducible_trans.
        { eapply reducible_app_1; eassumption. }
        { apply reducible_refl. }
      * simpl; omega.
    + exists ins, (hst :: atms), outs.
      repeat split; auto.
      * constructor; auto.
        red; eauto.
      * eapply reducible_trans.
        { eapply reducible_app_1; eassumption. }
        { simpl; repeat rewrite app_assoc.
          do 2 apply reducible_app_2.
          apply atomic_internal_history in H2.
          clear -H1 H2.
          induction outs; simpl; [rewrite app_nil_r; apply reducible_refl|].
          inv H1.
          destruct a as [| | |eouts]; try (intuition; fail).
          eapply reducible_trans.
          { replace (hst ++ RlblOuts eouts :: outs) with ((hst ++ [RlblOuts eouts]) ++ outs)
              by (rewrite <-app_assoc; reflexivity).
            eapply reducible_app_2.
            eapply outs_reducible.
            apply Forall_impl with (P:= @InternalLbl _); auto.
            intros; destruct a; intuition.
          }
          { apply reducible_cons; auto. }
        }
      * simpl; omega.
Qed.
  
(* NOTE: For the reducibility of internal state transitions, see [Commutable.v]. *)

Close Scope list.

