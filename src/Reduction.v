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

Definition Internal (lbl: MLabel) :=
  match lbl with
  | RlblInt _ _ _ => True
  | _ => False
  end.

Definition InternalHistory (hst: History) :=
  Forall (fun tlbl => Internal tlbl) hst.

Lemma msg_ins_commutes:
  forall sys st1 eins lbl st2,
    Internal lbl ->
    steps step_m sys st1 [RlblIns eins; lbl] st2 ->
    steps step_m sys st1 [lbl; RlblIns eins] st2.
Proof.
  intros.
  destruct lbl as [|hdl mins mouts|]; [elim H| |elim H].
  dest_step_m.
  - econstructor.
    + econstructor.
      * econstructor. 
      * econstructor; eauto. 
    + econstructor.
  - econstructor.
    + econstructor.
      * econstructor. 
      * econstructor; eauto. 
    + econstructor; try reflexivity; try eassumption.
      * clear -H9; induction mins; simpl; [constructor|].
        inv H9; constructor; auto.
        apply FirstMP_enqMsgs; auto.
      * f_equal.
        admit. (* requires a lemma about [MessagePool] *)
Admitted.

Lemma msg_in_reduced:
  forall sys st1 eins hst2 st2,
    steps step_m sys st1 (RlblIns eins :: hst2) st2 ->
    InternalHistory hst2 ->
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
    InternalHistory hst2 ->
    steps step_m sys st1 (hst1 ++ hst2 ++ [RlblIns eins]) st2.
Proof.
  intros.
  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  eapply msg_in_reduced in H; eauto.
  eapply steps_append; eauto.
Qed.

Lemma msg_outs_commutes:
  forall sys st1 eouts lbl st2,
    Internal lbl ->
    steps step_m sys st1 [lbl; RlblOuts eouts] st2 ->
    steps step_m sys st1 [RlblOuts eouts; lbl] st2.
Proof.
  intros.
  destruct lbl as [|hdl mins mouts|]; [elim H| |elim H].
  dest_step_m.
  - econstructor.
    + econstructor.
      * econstructor. 
      * econstructor; eauto. 
    + econstructor; eauto.
  - econstructor.
    + econstructor.
      * econstructor. 
      * econstructor; try reflexivity; try eassumption.
        admit. (* requires a lemma about [MessagePool] *)
    + econstructor; try reflexivity; try eassumption.
      * admit. (* requires a lemma about [MessagePool] *)
      * f_equal.
        admit. (* requires a lemma about [MessagePool] *)
Admitted.

Lemma msg_outs_reduced:
  forall sys st1 eouts hst2 st2,
    steps step_m sys st1 (hst2 ++ [RlblOuts eouts]) st2 ->
    InternalHistory hst2 ->
    steps step_m sys st1 (RlblOuts eouts :: hst2) st2.
Proof.
  induction hst2 as [|lbl ?]; simpl; intros; auto.
  inv H0; inv H.
  specialize (IHhst2 _ H5 H4).
  assert (steps step_m sys st1 (lbl :: RlblOuts eouts :: hst2) st2)
    by (econstructor; eauto).
  change (lbl :: RlblOuts eouts :: hst2) with
      ([lbl; RlblOuts eouts] ++ hst2) in H.
  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  change (RlblOuts eouts :: lbl :: hst2) with
      ([RlblOuts eouts; lbl] ++ hst2).
  eapply steps_append; eauto.
  eapply msg_outs_commutes; eauto.
Qed.

Lemma msg_outs_reduced_app:
  forall sys st1 hst1 eouts hst2 st2,
    steps step_m sys st1 (hst1 ++ hst2 ++ [RlblOuts eouts]) st2 ->
    InternalHistory hst2 ->
    steps step_m sys st1 (hst1 ++ RlblOuts eouts :: hst2) st2.
Proof.
  intros.
  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  eapply msg_outs_reduced in H; eauto.
  eapply steps_append; eauto.
Qed.

