Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM SemFacts.
Require Import Serial.

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
    steps step_m sys st1 hto st2.

(*! General Facts *)

Lemma reduced_app_1:
  forall sys hfr hto,
    Reduced sys hfr hto ->
    forall hst,
      Reduced sys (hst ++ hfr) (hst ++ hto).
Proof.
  unfold Reduced; intros.
  eapply steps_split in H0; [|reflexivity]; dest.
  eapply steps_append; eauto.
Qed.

Lemma reduced_app_2:
  forall sys hfr hto,
    Reduced sys hfr hto ->
    forall hst,
      Reduced sys (hfr ++ hst) (hto ++ hst).
Proof.
  unfold Reduced; intros.
  eapply steps_split in H0; [|reflexivity]; dest.
  eapply steps_append; eauto.
Qed.

(* Lemma reduced_serializable: *)
(*   forall sys hfr, *)
(*     Serializable sys hfr -> *)
(*     forall hto, *)
(*       Reduced sys hfr hto -> *)
(*       Serializable sys hto. *)

(*! Facts to prove serializability *)

Lemma msg_ins_commutes:
  forall sys eins lbl,
    Internal lbl ->
    Reduced sys [RlblIns eins; lbl] [lbl; RlblIns eins].
Proof.
  unfold Reduced; intros.
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
  forall sys eins hst2,
    InternalHistory hst2 ->
    Reduced sys (RlblIns eins :: hst2) (hst2 ++ [RlblIns eins]).
Proof.
  unfold Reduced; induction hst2 as [|lbl ?]; simpl; intros; auto.
  inv H.
  change (RlblIns eins :: lbl :: hst2) with ([RlblIns eins; lbl] ++ hst2) in H0.
  eapply steps_split in H0; [|reflexivity].
  destruct H0 as [sti [? ?]].
  eapply msg_ins_commutes in H0; [|assumption].
  pose proof (steps_append H H0); inv H1.
  specialize (IHhst2 H4 _ _ H7).
  econstructor; eauto.
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

