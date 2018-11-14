Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepM StepT SemFacts.
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
      ginv ist1 ->
      forall lbl ist2,
        trsSteps impl ist1 lbl ist2 ->
        ginv ist2.

  Definition InvSeq :=
    forall ist1,
      ginv ist1 ->
      forall lbl ist2,
        seqSteps impl ist1 lbl ist2 ->
        ginv ist2.

  Hypotheses (Hinvi: InvInit)
             (Hinvt: InvTrs).

  Lemma inv_trs_seqSteps':
    forall ist1,
      ginv ist1 ->
      forall ihst ist2,
        seqSteps impl ist1 ihst ist2 ->
        ginv ist2.
  Proof.
    intros.
    destruct H0; destruct H1 as [trss ?].
    destruct H1; subst.

    generalize dependent ist2; generalize dependent ist1.
    induction trss; simpl; intros.
    - inv H0; assumption.
    - eapply steps_split in H0; [|reflexivity].
      destruct H0 as [sti [? ?]].
      inv H1.
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
  forall {oifc} (impl: System oifc) ginv,
    InvInit impl ginv ->
    InvSeq impl ginv ->
    SerializableSys impl ->
    InvSteps impl step_m ginv.
Proof.
  unfold InvInit, InvSeq, SerializableSys, InvSteps, Invariant.InvSteps.
  intros.
  specialize (H1 _ _ H2).
  red in H1; destruct H1 as [sll ?].
  eapply H0; eauto.
Qed.

