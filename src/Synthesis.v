Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics SemFacts.
Require Import StepDet StepSeq Serial SerialFacts Simulation.

Section SimP.

  (** User inputs *)
  Variables
    (impl0 spec: System)
    (R: TState -> TState -> Prop)
    (p: Label -> Label).
  
  Definition SynthOk (s: System) :=
    Serial s step_det /\
    R (getStateInit s) (getStateInit spec) /\
    Simulates step_seq step_det R p s spec.

  Hypothesis (Hinit_ok: SynthOk impl0).

  Section SynthesisStep.

    Variable syn: System -> System -> Prop.
    Infix "↪" := syn (at level 30).

    (** The synthesizer [syn] should "preserve" three conditions:
     * 1) initial state
     * 2) serializability
     * 3) simulation on sequential semantics
     *)
    Hypotheses (Hsyn_init: forall s s', syn s s' -> getStateInit s' = getStateInit s)
               (Hsyn_serial:
                  forall s, Serial s step_det ->
                            forall s', syn s s' -> Serial s' step_det)
               (Hsyn_sim:
                  forall s, Simulates step_seq step_det R p s spec ->
                            forall s', syn s s' ->
                                       Simulates step_seq step_det R p s' spec).

    Lemma synthOk_refinement:
      forall s, SynthOk s -> step_det # step_det |-- s ⊑[p] spec.
    Proof.
      unfold SynthOk; intros; dest.
      eapply refines_trans.
      - apply sequential_step_seq.
        eauto using Hsyn_serial.
      - apply simulation_implies_refinement with (sim:= R); assumption.
    Qed.

    Lemma synthOk_preserved:
      forall s s', SynthOk s -> syn s s' -> SynthOk s'.
    Proof.
      unfold SynthOk; intros; dest.
      repeat split; eauto.
      erewrite Hsyn_init; eauto.
    Qed.

  End SynthesisStep.

End SimP.

