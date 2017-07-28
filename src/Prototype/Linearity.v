Require Import Bool List String Peano_dec.
Require Import FnMap Language.

Section History.
  Variables MsgT StateT: Type.

  Definition Nonlinearizable (hst: list (MsgId MsgT)) :=
    forall ehst,
      ExtHistory hst ehst ->
      forall lhst,
        Equivalent (complete ehst) lhst ->
        Concurrent lhst.

  Lemma nonlinearizable_not_linearizable:
    forall hst, Nonlinearizable hst ->
                forall lhst, ~ Linearizable hst lhst.
  Proof.
    unfold Nonlinearizable, Linearizable; intros.
    intro Hx; destruct Hx as [ehst [? [? ?]]].
    specialize (H _ H0 _ H2).
    auto.
  Qed.

  Lemma nonlinearizable_ext:
    forall hst,
      Nonlinearizable hst ->
      forall ehst, ExtHistory hst ehst -> Nonlinearizable ehst.
  Proof.
    unfold Nonlinearizable; intros.
    eauto.
  Qed.

End History.

