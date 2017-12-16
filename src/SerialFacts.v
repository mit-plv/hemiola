Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap.
Require Import Syntax Semantics SemFacts StepDet Serial.

Set Implicit Arguments.

Lemma atomic_nil_in:
  forall sys min mouts,
    Atomic sys min nil mouts ->
    forall msg,
      In msg mouts ->
      msg = min.
Proof.
  intros; inv H.
  Common.dest_in.
  reflexivity.
Qed.

Lemma atomic_emptyILabel_not_in:
  forall sys min hst mouts,
    Atomic sys min hst mouts ->
    ~ In emptyILabel hst.
Proof.
  induction 1; simpl; intros; [auto|].
  intro Hx; elim IHAtomic; destruct Hx.
  - discriminate.
  - assumption.
Qed.

Lemma atomic_iLblIn_not_in:
  forall sys min hst mouts,
    Atomic sys min hst mouts ->
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

