Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap.
Require Import Syntax Semantics SemFacts StepDet Serial.

Set Implicit Arguments.

Lemma atomic_nil_in:
  forall sys tid min mouts,
    Atomic sys tid min nil mouts ->
    forall msg,
      In msg mouts ->
      msg = min.
Proof.
  intros; inv H.
  Common.dest_in.
  reflexivity.
Qed.

Lemma steps_det_atomic_outs_ts:
  forall sys tid min ll mouts,
    Atomic sys tid min ll mouts ->
    forall st1 st2,
      steps_det sys st1 ll st2 ->
      Forall (fun tmsg => tmsg_tid tmsg = Some tid) mouts.
Proof.
  induction 1; simpl; intros.
  - repeat constructor; auto.
  - inv H1; apply Forall_app.
    + apply Forall_remove; eauto.
    + apply step_det_outs_tid in H7; dest; auto.
      specialize (IHAtomic _ _ H5).
      eapply Forall_forall in IHAtomic; [|eassumption].
      rewrite <-IHAtomic; auto.
Qed.

Lemma steps_det_atomic_outs_fwd_tid:
  forall sys tid min ll mouts,
    Atomic sys tid min ll mouts ->
    forall st1 st2,
      steps_det sys st1 ll st2 ->
      Forall (fun l => match l with
                       | IlblOuts (Some hdl) _ => tmsg_tid hdl = Some tid
                       | _ => False
                       end) ll.
Proof.
  induction 1; simpl; intros; [constructor|].
  inv H1.
  constructor; eauto.
  eapply steps_det_atomic_outs_ts in H; [|eassumption].
  eapply Forall_forall in H; eauto.
Qed.

Theorem serializable_seqSteps_refines:
  forall sys,
    SerializableSys sys ->
    steps_det # seqSteps |-- sys ⊑[id] sys.
Proof.
  unfold SerializableSys, Refines; intros.
  inv H0; rename ll0 into ill.
  specialize (H _ _ H1).

  unfold Serializable in H.
  destruct H as [sll [sst [? ?]]].

  rewrite H0.
  econstructor; eauto.
  apply map_id.
Qed.

