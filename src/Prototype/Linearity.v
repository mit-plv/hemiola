Require Import Bool List String Peano_dec.
Require Import FnMap Language.

Section History.
  Variables MsgT StateT: Type.

  Local Notation MsgId := (MsgId MsgT).
  Local Notation Object := (Object MsgT StateT).
  Local Notation Objects := (Objects MsgT StateT).

  (* Inductive Transactional: Objects -> list MsgId -> Prop := *)
  (* | TrsBase: *)
  (*     forall obs erq ers, *)
  (*       msg_rqrs erq = Rq -> *)
  (*       isTrsPair erq ers = true -> *)
  (*       isExternal (getIndices obs) (msgFrom erq) = true -> *)
  (*       isExternal (getIndices obs) (msgTo ers) = true -> *)
  (*       Transactional obs (ers :: erq :: nil) *)

  Definition Nonlinearizable (hst: list MsgId) :=
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

