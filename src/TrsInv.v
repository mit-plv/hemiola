Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepM SemFacts.
Require Import Invariant Serial SerialFacts.

Require Import Omega.

Set Implicit Arguments.

Section TrsInv.
  Context {oifc: OStateIfc}.

  Variables (impl: System oifc)
            (ginv: MState oifc -> Prop).

  Definition Invariant := @Invariant (MState oifc).
  Definition InvInit := @InvInit (System oifc) (MState oifc) _ impl ginv.

  Definition InvTrs :=
    forall ist1,
      Reachable (steps step_m) impl ist1 ->
      ginv ist1 ->
      forall hst ist2,
        trsSteps impl ist1 hst ist2 ->
        ginv ist2.

  Definition InvSeq :=
    forall ist1,
      Reachable (steps step_m) impl ist1 ->
      ginv ist1 ->
      forall hst ist2,
        seqSteps impl ist1 hst ist2 ->
        ginv ist2.

  Hypotheses (Hinvi: InvInit)
             (Hinvt: InvTrs).

  Lemma inv_trs_seqSteps':
    forall ist1,
      Reachable (steps step_m) impl ist1 ->
      ginv ist1 ->
      forall ihst ist2,
        seqSteps impl ist1 ihst ist2 ->
        ginv ist2.
  Proof.
    intros.
    destruct H1; destruct H2 as [trss ?].
    destruct H2; subst.

    generalize dependent ist2; generalize dependent ist1.
    induction trss; simpl; intros.
    - inv H1; assumption.
    - eapply steps_split in H1; [|reflexivity].
      destruct H1 as [sti [? ?]].
      inv H2.
      eapply Hinvt with (ist1:= sti); eauto.
      + eapply reachable_steps; eauto.
      + split; eauto.
  Qed.

  Lemma inv_trs_seqSteps: InvSeq.
  Proof.
    unfold InvSeq; intros.
    eapply inv_trs_seqSteps'; eauto.
  Qed.

End TrsInv.

Theorem invSeq_serializable_invStep:
  forall {oifc} (impl: System oifc) ginv,
    InvInit impl ginv ->
    InvSeq impl ginv ->
    SerializableSys impl ->
    InvStep impl step_m ginv.
Proof.
  unfold InvInit, InvSeq, SerializableSys, InvStep, Invariant.InvStep.
  intros.
  red in H2; destruct H2 as [ll ?].
  specialize (H1 _ _ (StepsCons H2 _ _ H4)).
  red in H1; destruct H1 as [sll ?].
  eapply H0; [| |eassumption]; auto.
  apply reachable_init.
Qed.

