Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics SemDet SemSeq Serial.

Set Implicit Arguments.

Lemma steps_history:
  forall sys step tr st,
    steps step sys (getStateInit sys) tr st ->
    HistoryOf sys step (historyOf tr).
Proof.
  intros.
  econstructor; eauto.
Qed.

Theorem sequential_step_seq:
  forall sys,
    Serial sys step_mod -> step_mod # step_seq |-- sys ⊑[id] sys.
Proof.
  unfold Serial, Refines; intros.
  rewrite map_id.
  inv H0; rename ll0 into ill. (* ill: the interleaving label sequence *)
  pose proof (steps_history H1); clear H1 st.
  specialize (H _ H0); destruct H as [shst [? ?]]; clear H0.

  inv H.
  inv H1.
Admitted.

