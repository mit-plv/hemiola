Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepDet Serial.
Require Import Synthesis TrsInv TrsSim.

(* Lemma what_we_want_using_atomic_rules: *)
(*   forall impl ti hst mouts orsout, *)
(*     Atomic impl ti (ilbl :: hst) mouts orsout -> *)
(*     forall pist ist1, *)
(*       steps_det impl pist hst ist1 -> *)
(*       step_det impl ist1 ilbl ist2 -> *)
(*       AtomicRules impl trsIdx rqin rqs .. *)

Section AtomicRules.

  Variables
    (impl: System)
    (trsIdx: IdxT)
    (rqin: Msg).

End AtomicRules.

