Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics Simulation.

Section Synthesis.

  (** Requirements *)
  Variables
    (step: System -> State -> Label -> State -> Prop)
    (impl0 spec: System) (* an initial system and the spec *)
    (R: State -> State -> Prop)
    (P: BLabel -> BLabel)
    (Hrinit: R (getStateInit impl0) (getStateInit spec))
    (Hsim: Simulates step R P impl0 spec). (* a simulation relation *)

  Lemma impl0_ok: step |-- impl0 ⊑[P] spec.
  Proof.
    eapply simulation_implies_refinement; eauto.
  Qed.

End Synthesis.

