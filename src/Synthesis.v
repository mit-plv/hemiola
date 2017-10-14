Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics Simulation.

Section Synthesis.

  (** Requirements *)
  Variables
    (stepI stepS: Step TState TLabel)
    (impl0 spec: System) (* an initial system and the spec *)
    (R: TState -> TState -> Prop)
    (p: Label -> Label)
    (Hrinit: R (getStateInit impl0) (getStateInit spec))
    (Hsim: Simulates stepI stepS R p impl0 spec). (* a simulation relation *)

  Lemma impl0_ok: stepI # stepS |-- impl0 ⊑[p] spec.
  Proof.
    eapply simulation_implies_refinement; eauto.
  Qed.

End Synthesis.

