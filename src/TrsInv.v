Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepM StepT SemFacts.
Require Import Invariant Serial SerialFacts.

Require Import Omega.

Set Implicit Arguments.

Section TrsInv.
  Variables (StateI MsgT: Type).
  Hypothesis (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2}).
  Context `{HasInit System StateI} `{HasMsg MsgT}.

  Variable (impl: System).

  Variables (stepI: Step StateI (RLabel MsgT))
            (ginv: StateI -> Prop).

  Definition Invariant := @Invariant StateI.
  Definition InvInit := @InvInit StateI _ impl ginv.

  Definition InvTrs :=
    forall ist1,
      ginv ist1 ->
      forall lbl ist2,
        trsSteps msgT_dec stepI impl ist1 lbl ist2 ->
        ginv ist2.

  Definition InvSeq :=
    forall ist1,
      ginv ist1 ->
      forall lbl ist2,
        seqSteps msgT_dec stepI impl ist1 lbl ist2 ->
        ginv ist2.

  Hypotheses (Hinvi: InvInit)
             (Hinvt: InvTrs).

  Lemma inv_trs_seqSteps':
    forall ist1,
      ginv ist1 ->
      forall ihst ist2,
        seqSteps msgT_dec stepI impl ist1 ihst ist2 ->
        ginv ist2.
  Proof.
    intros.
    destruct H2; destruct H3 as [trss ?].
    destruct H3; subst.

    generalize dependent ist2; generalize dependent ist1.
    induction trss; simpl; intros.
    - inv H2; assumption.
    - eapply steps_split in H2; [|reflexivity].
      destruct H2 as [sti [? ?]].
      inv H3.
      eapply Hinvt with (ist1:= sti); eauto.
      split; eauto.
  Qed.

  Lemma inv_trs_seqSteps: InvSeq.
  Proof.
    unfold InvSeq; intros.
    eapply inv_trs_seqSteps'; eauto.
  Qed.

End TrsInv.

Theorem invSeq_serializable_invSteps:
  forall impl ginv,
    InvInit impl ginv ->
    InvSeq msg_dec impl step_m ginv ->
    SerializableSys impl ->
    InvSteps impl step_m ginv.
Proof.
  unfold InvInit, InvSeq, SerializableSys, InvSteps, Invariant.InvSteps.
  intros.
  specialize (H1 _ _ H2).
  red in H1; destruct H1 as [sll ?].
  eapply H0; eauto.
Qed.

