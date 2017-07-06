Require Import List String Peano_dec.
Require Import FnMap Language SingleValue.

Theorem impl_serial: SerialObjects impl.
Proof.
  unfold SerialObjects, HistoryOf, Serializable; intros.
  destruct H as [oss [oims ?]].

Admitted.
