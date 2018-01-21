Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap.
Require Import Syntax Semantics SemFacts StepDet Serial.

Set Implicit Arguments.

Lemma SubHistory_refl:
  forall hst, SubHistory hst hst.
Proof.
  intros; exists nil; reflexivity.
Qed.

Lemma SubHistory_cons:
  forall l hst, SubHistory hst (l :: hst).
Proof.
  intros; exists (l :: nil); reflexivity.
Qed.

Lemma SubHistory_In:
  forall l hst1 hst2,
    In l hst1 ->
    SubHistory hst1 hst2 ->
    In l hst2.
Proof.
  unfold SubHistory; intros.
  destruct H0 as [nhsg ?]; subst.
  apply in_or_app; auto.
Qed.

Lemma atomic_emptyILabel_not_in:
  forall sys rqin hst mouts orsout,
    Atomic sys rqin hst mouts orsout ->
    ~ In emptyILabel hst.
Proof.
  induction 1; simpl; intros; [auto| |];
    try (intro Hx; elim IHAtomic; destruct Hx;
         [discriminate|assumption]).
Qed.

Lemma atomic_iLblIn_not_in:
  forall sys rqin hst mouts orsout,
    Atomic sys rqin hst mouts orsout ->
    forall msg,
      ~ In (IlblIn msg) hst.
Proof.
  induction 1; simpl; intros; [auto| |];
    try (intro Hx; destruct Hx;
         [discriminate|firstorder]).
Qed.

Lemma atomic_preserved:
  forall impl1 rqin hst mouts orsout,
    Atomic impl1 rqin hst mouts orsout ->
    forall impl2,
      indicesOf impl1 = indicesOf impl2 ->
      Atomic impl2 rqin hst mouts orsout.
Proof.
  induction 1; simpl; intros.
  - econstructor; eauto.
    unfold isExternal in *.
    rewrite H1 in H; assumption.
  - constructor; auto.
    unfold isInternal in *.
    rewrite H2 in H1; assumption.
  - constructor; auto.
    unfold isExternal in *.
    rewrite H1 in H0; assumption.
Qed.

Lemma atomic_rs_out:
  forall sys rqin hdl rsout hst mouts orsout,
    Atomic sys rqin (IlblOuts (Some hdl) (rsout :: nil) :: hst) mouts orsout ->
    isExternal sys (mid_to (msg_id (tmsg_msg rsout))) = true ->
    mouts = nil /\ orsout = Some rsout.
Proof.
  intros; inv H.
  - exfalso; inv H9.
    eapply internal_external_false; eauto.
  - auto.
Qed.

Lemma trsMessages_app:
  forall ti mp1 mp2,
    trsMessages ti (mp1 ++ mp2) =
    trsMessages ti mp1 ++ trsMessages ti mp2.
Proof.
  intros; apply filter_app.
Qed.

Lemma atomic_outs:
  forall sys rqin hst mouts orsout,
    Atomic sys rqin hst mouts orsout ->
    hst <> nil ->
    forall st1 st2,
      steps_det sys st1 hst st2 ->
      trsMessages rqin (tst_msgs st2) = mouts.
Proof.
  induction 1; simpl; intros; [intuition idtac| |].
  - inv H3.
    inv H9; simpl in *.
    unfold distributeMsgs.
    rewrite trsMessages_app.

    (* Hint: case analysis on [hst]:
     * - nil: invert H
     * - cons: use IHAtomic
     *)
    
Admitted.

Theorem serializable_seqSteps_refines:
  forall sys,
    SerializableSys sys ->
    steps_det # seqSteps |-- sys ⊑[id] sys.
Proof.
  unfold SerializableSys, Refines; intros.
  inv H0; rename ll0 into ill.
  specialize (H _ _ H1).
  unfold Serializable in H.
  destruct H as [sll [sst [? ?]]].
  rewrite H0.
  econstructor; eauto.
  apply map_id.
Qed.

