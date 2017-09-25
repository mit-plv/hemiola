Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics SemDet SemSeq Serial.

Theorem sequential_step_seq:
  forall sys,
    Serial step_det sys ->
    step_det # step_seq |-- sys ⊑[id] sys.
Proof.
Admitted.

