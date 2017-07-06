Require Import List String Peano_dec.
Require Import Language SingleValue.

Theorem impl_serial: SerialObjects svm_is_req impl.
Proof.
  unfold SerialObjects, HistoryOf, Serializable; intros.
Admitted.
