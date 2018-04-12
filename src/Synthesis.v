Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics SemFacts.
Require Import StepT Serial SerialFacts Invariant TrsSim.

Set Implicit Arguments.

Section SynthOk.

  (** User inputs *)
  Variables
    (impl0 spec: System)
    (R: TState -> TState -> Prop)
    (ginv: TState -> Prop)
    (p: Label -> Label).

  (* NOTE: the order here matters. [Rule]s are synthesized during the simulation
   * proof. Invariants are proven after all [Rule]s are synthesized.
   *)
  Definition SynthOk (s: System) :=
    R initsOf initsOf /\
    ginv initsOf /\
    (TrsSimulates R ginv p s spec /\ InvStep s step_t ginv) /\
    SerializableSys s.

  Hypothesis (Hinit_ok: SynthOk impl0).

  Section SynthesisStep.

    Definition SynT := System -> System -> Prop.
    Variable syn: SynT.

    (** The synthesizer [syn] should "preserve" three conditions:
     * 1) initial state
     * 2) serializability
     * 3) simulation on sequential semantics
     * 4) global invariants
     *)
    Hypotheses (HsynSerial:
                  forall s, SerializableSys s ->
                            forall s', syn s s' -> SerializableSys s')
               (HsynSim:
                  forall s, TrsSimulates R ginv p s spec ->
                            forall s', syn s s' -> TrsSimulates R ginv p s' spec)
               (HsynInv:
                  forall s, InvStep s step_t ginv ->
                            forall s', syn s s' -> InvStep s' step_t ginv).

    Lemma synthOk_refinement:
      forall s, SynthOk s -> steps step_t # steps step_t |-- s ⊑[p] spec.
    Proof.
      unfold SynthOk; intros; dest.
      eapply refines_trans.
      - apply serializable_seqSteps_refines in H2.
        eassumption.
      - eapply sequential_simulation_implies_refinement; eauto.
    Qed.

    Lemma synthOk_preserved:
      forall s s', SynthOk s -> syn s s' -> SynthOk s'.
    Proof.
      unfold SynthOk; intros; dest.
      repeat split; eauto.
    Qed.

  End SynthesisStep.

End SynthOk.

Definition rqChn: IdxT := 0.
Definition rsChn: IdxT := 1.
Definition numChns := S rsChn.

