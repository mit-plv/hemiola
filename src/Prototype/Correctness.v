Require Import Bool List String Peano_dec Eqdep.
Require Import FnMap Language SingleValue Transaction.

Section System.
  Variables extIdx1 extIdx2: nat.

  Theorem impl_linear: Linear (impl extIdx1 extIdx2).
  Proof.
  Admitted.

End System.

