Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM SemFacts.
Require Import Serial.

Require Import Permutation.

Set Implicit Arguments.

Ltac dest_step_m :=
  repeat match goal with
         | [H: steps step_m _ _ _ _ |- _] => inv H
         | [H: step_m _ _ _ _ |- _] => inv H
         | [H: {| bst_oss := _ |} = {| bst_oss := _ |} |- _] => inv H
         end; simpl in *.

Definition NonSilentHistory (hst: MHistory) :=
  Forall (fun lbl => lbl <> emptyRLabel _) hst.

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

Lemma internal_history_behavior_nil:
  forall sys hst,
    InternalHistory hst -> behaviorOf sys hst = nil.
Proof.
  induction hst; simpl; intros; auto.
  inv H; rewrite IHhst by assumption.
  destruct a; auto; elim H2.
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
    Serializable sys hfr ->
    forall hto,
      Reduced sys hfr hto ->
      Serializable sys hto.
Proof.
  unfold Serializable, Reduced; intros.
  destruct H0 as [shfr [stfr [? ?]]].
  exists shfr, stfr.
  split; auto.
  specialize (H1 _ _ H); dest.
  congruence.
Qed.

(*! Facts to prove serializability *)

Lemma msg_ins_commutes:
  forall sys eins lbl,
    Internal lbl ->
    Reduced sys [RlblIns eins; lbl] [lbl; RlblIns eins].
Proof.
  unfold Reduced; intros.
  split.
  - destruct lbl as [|hdl mins mouts|]; [elim H| |elim H].
    dest_step_m.
    + econstructor.
      * econstructor.
        { econstructor. } 
        { econstructor; eauto. }
      * econstructor.
    + econstructor.
      * econstructor.
        { econstructor. }
        { econstructor; eauto. }
      * econstructor; try reflexivity; try eassumption.
        { eapply FirstMPI_Forall_enqMsgs; eauto. }
        { f_equal.
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
        }
  - hnf; cbn.
    destruct lbl; [elim H|auto|elim H].
Qed.

Lemma msg_in_reduced:
  forall sys eins hst2,
    InternalHistory hst2 ->
    Reduced sys (RlblIns eins :: hst2) (hst2 ++ [RlblIns eins]).
Proof.
  unfold Reduced; induction hst2 as [|lbl ?]; simpl; intros;
    [split; [assumption|reflexivity]|].
  inv H.
  split.
  - change (RlblIns eins :: lbl :: hst2) with ([RlblIns eins; lbl] ++ hst2) in H0.
    eapply steps_split in H0; [|reflexivity].
    destruct H0 as [sti [? ?]].
    eapply msg_ins_commutes in H0; [|assumption]; dest.
    pose proof (steps_append H H0); inv H2.
    specialize (IHhst2 H4 _ _ H8); dest.
    econstructor; eauto.
  - red; cbn.
    rewrite behaviorOf_app.
    rewrite internal_history_behavior_nil by assumption.
    destruct lbl; auto; elim H3.
Qed.

Lemma msg_outs_commutes:
  forall sys eouts lbl,
    Internal lbl ->
    Reduced sys [lbl; RlblOuts eouts] [RlblOuts eouts; lbl].
Proof.
  unfold Reduced; intros.
  split.
  - destruct lbl as [|hdl mins mouts|]; [elim H| |elim H].
    dest_step_m.
    + econstructor.
      * econstructor.
        { econstructor. }
        { econstructor; eauto. }
      * econstructor; eauto.
    + econstructor.
      * econstructor.
        { econstructor. }
        { econstructor; try reflexivity; try eassumption.
          assert (DisjList (idsOf mins) (idsOf eouts)).
          { destruct H3, H12.
            eapply DisjList_SubList; eauto.
            eapply DisjList_comm, DisjList_SubList; eauto.
            apply DisjList_comm, mindsOf_merssOf_DisjList.
          }
          eapply FirstMPI_Forall_deqMsgs; eauto.
        }
      * assert (DisjList (idsOf eouts) (idsOf mins)).
        { destruct H3, H12.
          eapply DisjList_SubList; eauto.
          eapply DisjList_comm, DisjList_SubList; eauto.
          apply mindsOf_merssOf_DisjList.
        }
        econstructor; try reflexivity; try eassumption.
        { eapply FirstMPI_Forall_enqMsgs.
          rewrite <-FirstMPI_Forall_deqMsgs; eauto.
        }
        { f_equal; rewrite <-enqMsgs_deqMsgs_FirstMPI_comm.
          { f_equal; eapply deqMsgs_deqMsgs_comm.
            apply DisjList_comm; auto.
          }
          { destruct H3; auto. }
          { rewrite <-FirstMPI_Forall_deqMsgs; eauto. }
        }
  - hnf; cbn.
    destruct lbl; [elim H|auto|elim H].
Qed.

Lemma msg_outs_reduced:
  forall sys eouts hst2,
    InternalHistory hst2 ->
    Reduced sys (hst2 ++ [RlblOuts eouts]) (RlblOuts eouts :: hst2).
Proof.
  unfold Reduced; induction hst2 as [|lbl ?]; simpl; intros; 
    [split; [assumption|reflexivity]|].
  inv H0; inv H.
  split.
  - specialize (IHhst2 H3 _ _ H4); dest.
    assert (steps step_m sys st1 (lbl :: RlblOuts eouts :: hst2) st2)
      by (econstructor; eauto).
    change (lbl :: RlblOuts eouts :: hst2) with
        ([lbl; RlblOuts eouts] ++ hst2) in H1.
    eapply steps_split in H1; [|reflexivity].
    destruct H1 as [sti [? ?]].
    change (RlblOuts eouts :: lbl :: hst2) with
        ([RlblOuts eouts; lbl] ++ hst2).
    eapply steps_append; eauto.
    eapply msg_outs_commutes; eauto.
  - red; cbn.
    rewrite behaviorOf_app.
    rewrite internal_history_behavior_nil by assumption.
    destruct lbl; auto; elim H2.
Qed.

Lemma msg_int_commutes_1:
  forall sys rule1 ins1 outs1 rule2 ins2 outs2,
    Reduced sys [RlblInt rule2 ins2 outs2; RlblInt rule1 ins1 outs1]
            [RlblInt rule1 ins1 outs1; RlblInt rule2 ins2 outs2].
Proof.
Admitted.

Lemma msg_int_commutes_2:
  forall sys rule1 ins1 outs1 rule2 ins2 outs2 rule3 ins3 outs3,
    Reduced sys [RlblInt rule3 ins3 outs3;
                   RlblInt rule2 ins2 outs2;
                   RlblInt rule1 ins1 outs1]
            [RlblInt rule3 ins3 outs3;
               RlblInt rule1 ins1 outs1;
               RlblInt rule2 ins2 outs2].
Proof.
Admitted.

(* Lemma msg_int_commutes_2: *)
(*   forall sys eins lbl, *)
(*     Internal lbl -> *)
(*     Reduced sys [RlblIns eins; lbl] [lbl; RlblIns eins]. *)
(* Proof. *)


(* Theorem request_forwardings_reduced: *)
(*   forall rqr rqin rqfwds hsts, *)
(*     Forall (fun rqhst => exists houts, Atomic (fst rqhst) (snd rqhst) houts) *)
(*            (combine rqfwds hsts) -> *)
(*     forall sys indeps, *)
(*       Reduced sys (List.concat (indeps ++ hsts) ++ [RlblInt rqr [rqin] rqfwds]) *)
(*               nil. (* TODO *) *)
