Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics SemDet SemSeq Serial.

Theorem sequential_step_seq:
  forall sys tr,
    Behavior step_det sys tr ->
    Sequential (historyOf sys tr) ->
    Behavior step_seq sys tr.
Proof.
Admitted.

