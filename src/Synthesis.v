Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics SemFacts.
Require Import StepM StepT Serial SerialFacts Invariant TrsSim.

Set Implicit Arguments.

Section SynthOk.

  (** User inputs *)
  Variables
    (spec: System)
    (R: TState -> TState -> Prop)
    (ginv: TState -> Prop).

  (* NOTE: the order here matters. [Rule]s are synthesized during the simulation
   * proof. Invariants are proven after all [Rule]s are synthesized.
   *)
  Definition SynthOk (s: System) :=
    R (initsOf s) (initsOf spec) /\
    ginv (initsOf s) /\
    (TrsSimulates R ginv s spec /\ InvStep s step_t ginv) /\
    SerializableSys s.

  Lemma synthOk_refinement:
    forall s, SynthOk s -> steps step_m # steps step_m |-- s ⊑ spec.
  Proof.
    unfold SynthOk; intros; dest.
    eapply refines_trans.
    - apply serializable_seqSteps_refines in H2.
      eassumption.
    - (** TODO: connect [step_m] and [step_t] *)
      (* eapply sequential_simulation_implies_refinement; eauto. *)
      admit.
  Admitted.

  Section SynthesisStep.

    Definition SynT := System -> System -> Prop.
    Variable syn: SynT.

    (** The synthesizer [syn] should "preserve" three conditions:
     * 1) initial state
     * 2) serializability
     * 3) simulation on sequential semantics
     * 4) global invariants
     *)
    Hypotheses
      (HsynInit: forall s s', syn s s' -> initsOf (StateT:= TState) s =
                                          initsOf (StateT:= TState) s')
      (HsynSerial:
         forall s, SerializableSys s ->
                   forall s', syn s s' -> SerializableSys s')
      (HsynSim:
         forall s, TrsSimulates R ginv s spec ->
                   forall s', syn s s' -> TrsSimulates R ginv s' spec)
      (HsynInv:
         forall s, InvStep s step_t ginv ->
                   forall s', syn s s' -> InvStep s' step_t ginv).

    Lemma synthOk_preserved:
      forall s s', SynthOk s -> syn s s' -> SynthOk s'.
    Proof.
      unfold SynthOk; intros; dest.
      repeat split; eauto.
      - erewrite <-HsynInit; eauto.
      - erewrite <-HsynInit; eauto.
    Qed.

  End SynthesisStep.

End SynthOk.

