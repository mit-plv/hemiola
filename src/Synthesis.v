Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics Simulation.

Section Synthesis.

  (** Requirements *)
  Variables
    (impl0 spec: System) (* an initial system and the spec *)
    (R: State -> State -> Prop)
    (Hrinit: R (getStateInit impl0) (getStateInit spec))
    (Hsim: Simulates R impl0 spec). (* a simulation relation *)

  Lemma impl0_ok: impl0 ⊑ spec.
  Proof.
    eapply simulation_implies_refinement; eauto.
  Qed.

End Synthesis.

