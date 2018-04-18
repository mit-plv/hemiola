Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepT SemFacts.

Definition NonSilentHistory (hst: THistory) :=
  Forall (fun tlbl => tlbl <> emptyRLabel) hst.

Definition NotMsgIn {MsgT} (lbl: RLabel MsgT) :=
  match lbl with
  | RlblIn _ => False
  | _ => True
  end.

Definition NonMsgInHistory (hst: THistory) :=
  Forall (fun tlbl => NotMsgIn tlbl) hst.

Lemma msg_in_commutes:
  forall sys st1 emsg tlbl st2,
    NotMsgIn tlbl ->
    steps step_t sys st1 [RlblIn emsg; tlbl] st2 ->
    steps step_t sys st1 [tlbl; RlblIn emsg] st2.
Proof.
  intros.
  destruct tlbl as [|hdl mins mouts]; [elim H|].
  repeat match goal with
         | [H: steps step_t sys _ _ _ |- _] => inv H
         | [H: step_t sys _ _ _ |- _] => inv H
         end.
  - repeat econstructor; eauto.
  - econstructor.
    + repeat econstructor; eauto.
    + inv H7.
Admitted.

Lemma msg_in_reduced:
  forall sys st1 emsg hst2 st2,
    steps step_t sys st1 (RlblIn emsg :: hst2) st2 ->
    NonMsgInHistory hst2 ->
    steps step_t sys st1 (hst2 ++ [RlblIn emsg]) st2.
Proof.
  induction hst2 as [|tlbl ?]; intros; [assumption|].

  inv H0.
  change (RlblIn emsg :: tlbl :: hst2) with ([RlblIn emsg; tlbl] ++ hst2) in H.
  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  apply msg_in_commutes in H0; auto.
  pose proof (steps_append H H0); clear H H0.
  simpl in H1; inv H1.
  specialize (IHhst2 _ H5 H4).
  simpl; econstructor; eassumption.
Qed.

Lemma msg_in_reduced_app:
  forall sys st1 hst1 emsg hst2 st2,
    steps step_t sys st1 (hst1 ++ RlblIn emsg :: hst2) st2 ->
    NonMsgInHistory hst2 ->
    steps step_t sys st1 (hst1 ++ hst2 ++ [RlblIn emsg]) st2.
Proof.
  intros.
  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  apply msg_in_reduced in H; auto.
  eapply steps_append; eauto.
Qed.

