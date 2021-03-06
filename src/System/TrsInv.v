Require Import Bool List String PeanoNat.
Require Import Common FMap ListSupport Syntax Semantics StepM SemFacts.
Require Import Invariant Serial SerialFacts.

Require Import Lia.

Set Implicit Arguments.

Section TrsInv.
  Context `{dv: DecValue} `{oifc: OStateIfc}.

  Variables (impl: System)
            (ginv: State -> Prop).

  Definition Invariant := @Invariant (State).
  Definition InvInit := @InvInit (System) (State) _ impl ginv.

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

Section AtomicInv.
  Context `{dv: DecValue} `{oifc: OStateIfc}.

  Variables (impl: System)
            (ginv: State -> Prop)
            (ainv: list (Id Msg) (* inits *) ->
                   State (* starting state *) ->
                   History (* atomic history *) ->
                   list (Id Msg) (* eouts *) ->
                   State (* ending state *) -> Prop).

  Definition InvTrsIns :=
    forall ist1,
      Reachable (steps step_m) impl ist1 ->
      ginv ist1 ->
      forall eins ist2,
        step_m impl ist1 (RlblIns eins) ist2 ->
        ginv ist2.

  Definition InvTrsOuts :=
    forall ist1,
      Reachable (steps step_m) impl ist1 ->
      ginv ist1 ->
      forall eouts ist2,
        step_m impl ist1 (RlblOuts eouts) ist2 ->
        ginv ist2.

  Definition InvTrsAtomic :=
    forall ist1,
      Reachable (steps step_m) impl ist1 ->
      ginv ist1 ->
      forall inits hst eouts ist2,
        ExtAtomic impl inits hst eouts ->
        steps step_m impl ist1 hst ist2 ->
        ainv inits ist1 hst eouts ist2 /\ ginv ist2.

  Hypotheses (Hinvi: InvInit impl ginv)
             (Hinvti: InvTrsIns)
             (Hinvto: InvTrsOuts)
             (Hinvta: InvTrsAtomic).

  Lemma inv_atomic_InvTrs:
    InvTrs impl ginv.
  Proof.
    red; intros.
    destruct H1.
    inv H2.
    - inv_steps; inv_step; assumption.
    - inv_steps; eapply Hinvti; eauto.
    - inv_steps; eapply Hinvto; eauto.
    - eapply Hinvta; eauto.
  Qed.

End AtomicInv.

Theorem invSeq_serializable_invStep:
  forall `{dv: DecValue} `{oifc: OStateIfc} (impl: System) ginv,
    InvInit impl ginv ->
    InvSeq impl ginv ->
    SerializableSys impl ->
    InvStep impl step_m ginv.
Proof.
  unfold InvInit, InvSeq, SerializableSys, InvStep, Invariant.InvStep.
  intros.
  assert (Reachable (steps step_m) impl ist2).
  { eapply reachable_steps; [eassumption|].
    apply steps_singleton; eassumption.
  }
  specialize (H1 _ H5).
  red in H1; destruct H1 as [sll ?].
  eapply H0; [| |eassumption]; auto.
  apply reachable_init.
Qed.
