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
  forall sys rqin hst mouts,
    Atomic sys rqin hst mouts ->
    ~ In emptyILabel hst.
Proof.
  induction 1; simpl; intros; [auto|].
  intro Hx; elim IHAtomic; destruct Hx.
  - discriminate.
  - assumption.
Qed.

Lemma atomic_iLblIn_not_in:
  forall sys rqin hst mouts,
    Atomic sys rqin hst mouts ->
    forall msg,
      ~ In (IlblIn msg) hst.
Proof.
  induction 1; simpl; intros; [auto|].
  intro Hx; destruct Hx.
  - discriminate.
  - firstorder.
Qed.

Lemma atomic_preserved:
  forall impl1 min hst mouts,
    Atomic impl1 min hst mouts ->
    forall impl2,
      indicesOf impl1 = indicesOf impl2 ->
      Atomic impl2 min hst mouts.
Proof.
  induction 1; simpl; intros.
  - constructor; auto.
    unfold isExternal in *.
    rewrite H0 in H; assumption.
  - constructor; auto.
Qed.

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

