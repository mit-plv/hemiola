Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM SemFacts.

Set Implicit Arguments.

Ltac dest_step_m :=
  repeat match goal with
         | [H: steps step_m _ _ _ _ |- _] => inv H
         | [H: step_m _ _ _ _ |- _] => inv H
         | [H: {| bst_oss := _ |} = {| bst_oss := _ |} |- _] => inv H
         end; simpl in *.

Definition NonSilentHistory (hst: History) :=
  Forall (fun lbl => lbl <> emptyRLabel _) hst.

Definition NotMsgIn (lbl: MLabel) :=
  match lbl with
  | RlblIns _ => False
  | _ => True
  end.

Definition NonMsgInHistory (hst: History) :=
  Forall (fun tlbl => NotMsgIn tlbl) hst.

Lemma msg_ins_commutes:
  forall sys st1 eins lbl st2,
    NotMsgIn lbl ->
    steps step_m sys st1 [RlblIns eins; lbl] st2 ->
    steps step_m sys st1 [lbl; RlblIns eins] st2.
Proof.
  intros.
  destruct lbl as [|hdl mins mouts|]; [elim H| |].
  - dest_step_m.
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
        { admit. }
        { f_equal.
          admit.
        }
  - dest_step_m.
    econstructor.
    + econstructor.
      * econstructor.
      * econstructor; eauto.
    + econstructor; try reflexivity; try eassumption.
      * admit.
      * f_equal.
        admit.
Admitted.

Lemma msg_in_reduced:
  forall sys st1 eins hst2 st2,
    steps step_m sys st1 (RlblIns eins :: hst2) st2 ->
    NonMsgInHistory hst2 ->
    steps step_m sys st1 (hst2 ++ [RlblIns eins]) st2.
Proof.
  induction hst2 as [|lbl ?]; simpl; intros; auto.
  inv H0.
  change (RlblIns eins :: lbl :: hst2) with ([RlblIns eins; lbl] ++ hst2) in H.
  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  eapply msg_ins_commutes in H0; [|assumption].
  pose proof (steps_append H H0); inv H1.
  specialize (IHhst2 _ H7 H4).
  econstructor; eauto.
Qed.

Lemma msg_in_reduced_app:
  forall sys st1 hst1 eins hst2 st2,
    steps step_m sys st1 (hst1 ++ RlblIns eins :: hst2) st2 ->
    NonMsgInHistory hst2 ->
    steps step_m sys st1 (hst1 ++ hst2 ++ [RlblIns eins]) st2.
Proof.
  intros.
  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  eapply msg_in_reduced in H; eauto.
  eapply steps_append; eauto.
Qed.

