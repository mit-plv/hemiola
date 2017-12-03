Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap.
Require Import Syntax Semantics SemFacts StepDet StepSeq Serial.

Set Implicit Arguments.

Lemma transactional_cons_inv:
  forall sys a ll,
    Transactional sys (a :: ll) ->
    Transactional sys ll.
Proof.
  unfold Transactional; intros.
  destruct H as [ptid [pmin [pmouts [? ?]]]].
  inv H0.
  do 3 eexists; split; eauto.
Qed.

Corollary transactional_ocons_inv:
  forall sys oa ll,
    Transactional sys (oa ::> ll) ->
    Transactional sys ll.
Proof.
  destruct oa as [a|]; simpl; intros; auto.
  eauto using transactional_cons_inv.
Qed.

Lemma atomic_nil_in:
  forall tid min mouts,
    Atomic tid min nil mouts ->
    forall msg,
      In msg mouts ->
      msg = min.
Proof.
  intros; inv H.
  Common.dest_in.
  reflexivity.
Qed.

Lemma step_det_seq_in:
  forall sys st1 msg st2,
    step_det sys st1 (IlblIn msg) st2 ->
    step_seq sys st1 (IlblIn msg) st2.
Proof.
  intros; inv H.
  constructor; auto.
Qed.

Lemma steps_det_atomic_outs_ts:
  forall tid min ll mouts,
    Atomic tid min ll mouts ->
    forall sys st1 st2,
      steps step_det sys st1 ll st2 ->
      Forall (fun tmsg => tmsg_tid tmsg = Some tid) mouts.
Proof.
  induction 1; simpl; intros.
  - repeat constructor; auto.
  - inv H1; apply Forall_app.
    + apply Forall_remove; eauto.
    + apply step_det_outs_tid in H7; dest; auto.
      specialize (IHAtomic _ _ _ H5).
      eapply Forall_forall in IHAtomic; [|eassumption].
      rewrite <-IHAtomic; auto.
Qed.

Lemma steps_det_atomic_outs_fwd_tid:
  forall tid min ll mouts,
    Atomic tid min ll mouts ->
    forall sys st1 st2,
      steps step_det sys st1 ll st2 ->
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

Lemma transactional_steps_seq:
  forall sys ll,
    Transactional sys ll ->
    forall st1 st2,
      steps step_det sys st1 ll st2 ->
      steps step_seq sys st1 ll st2.
Proof.
  induction ll as [|l ll]; simpl; intros; subst;
    [inv H0; constructor|].

  specialize (IHll (transactional_cons_inv H)).

  destruct H as [tid [trin [trouts [? ?]]]].
  pose proof (steps_det_atomic_outs_fwd_tid H1 H0).

  inv H0.
  specialize (IHll _ _ H6).
  econstructor; eauto.

  inv H2.
  destruct l; [intuition idtac|].
  destruct mhdl; [|intuition idtac].

  destruct ll.
  - inv H1; inv H11; inv H6.
    Common.dest_in.
    inv H8.
    + econstructor; eauto.
    + exfalso; simpl in H9; eauto using internal_external_false.
  - inv H1; inv H11; inv H5.
    inv H8.
    + exfalso.
      inv IHll.
      apply step_seq_outs_tid in H22; simpl in H22; dest.
      simpl in H4; inv H4.
      rewrite H0 in H2; inv H2.
      intuition.
    + assert (ts = mts); subst.
      { inv IHll.
        apply step_seq_outs_tid in H22; simpl in H22; dest.
        rewrite H14 in H4; inv H4.
        rewrite H0 in H2; inv H2.
        reflexivity.
      }
      econstructor; eauto.
Qed.

Lemma sequential_steps:
  forall sys ll,
    Sequential sys ll ->
    forall st,
      steps step_det sys (getStateInit sys) ll st ->
      steps step_seq sys (getStateInit sys) ll st.
Proof.
  induction 1; simpl; intros; subst.
  - inv H; constructor.
  - inv H1.
    econstructor; eauto.
    apply step_det_seq_in; auto.
  - eapply steps_split in H1; [|reflexivity].
    destruct H1 as [sti ?]; dest.
    apply steps_append with (st2:= sti); auto.
    auto using transactional_steps_seq.
Qed.

Theorem serializable_step_seq:
  forall sys ll st,
    steps step_det sys (getStateInit sys) ll st ->
    Serializable sys step_det ll ->
    Behavior step_seq sys (behaviorOf sys ll).
Proof.
  unfold Serializable; intros.
  destruct H0 as [sll [sst [? [? ?]]]].
  pose proof (sequential_steps H1 H0) as Hseq.
  eapply Behv; eauto.
Qed.

Theorem sequential_step_seq:
  forall sys,
    SerializableSys sys step_det ->
    step_det # step_seq |-- sys ⊑[id] sys.
Proof.
  unfold SerializableSys, Refines; intros.
  inv H0; rename ll0 into ill. (* ill: the interleaving label sequence *)
  specialize (H _ _ H1).
  rewrite map_id.
  eauto using serializable_step_seq.
Qed.

