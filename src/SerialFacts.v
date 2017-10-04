Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics SemDet SemSeq Serial.

Set Implicit Arguments.

Lemma equiv_history_behavior:
  forall sys lla sta llb stb,
    steps step_mod sys (getStateInit sys) lla sta ->
    steps step_mod sys (getStateInit sys) llb stb ->
    historyOf lla ≡ historyOf llb ->
    exists ll,
      steps step_mod sys (getStateInit sys) ll stb /\
      historyOf ll = historyOf llb /\
      behaviorOf ll = behaviorOf lla.
Proof.
Admitted.

(* Lemma sequential_steps: *)
(*   forall sys ll st, *)
(*     Sequential sys (historyOf ll) -> *)
(*     steps step_mod sys (getStateInit sys) ll st -> *)
(*     steps step_seq sys (getStateInit sys) ll st. *)
(* Proof. *)
(*   unfold Sequential; intros. *)
(*   destruct H as [trs [? ?]]. *)

(* Admitted. *)

Theorem serializable_step_seq:
  forall sys ll st,
    steps step_mod sys (getStateInit sys) ll st ->
    Serializable sys step_mod ll ->
    Behavior step_seq sys (behaviorOf ll).
Proof.
  (* unfold Serializable; intros. *)
  (* destruct H0 as [sll [sst [? [? ?]]]]. *)

  (* pose proof (equiv_history_behavior H H0 H2) as Hnll. *)
  (* destruct Hnll as [nll [? [? ?]]]. *)

  (* eapply Behv with (st:= sst) (ll:= nll); eauto. *)

  (* rewrite <-H4 in H1. *)
  (* auto using sequential_steps. *)
Admitted.

Theorem sequential_step_seq:
  forall sys,
    Serial sys step_mod -> step_mod # step_seq |-- sys ⊑[id] sys.
Proof.
  unfold Serial, Refines; intros.
  rewrite map_id.
  inv H0; rename ll0 into ill. (* ill: the interleaving label sequence *)
  specialize (H _ _ H1).
  eauto using serializable_step_seq.
Qed.

