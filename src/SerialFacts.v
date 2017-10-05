Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics SemFacts SemDet SemSeq Serial.

Set Implicit Arguments.

Definition NonActive (ll: list Label) :=
  Forall (fun l => match l with
                   | LblHdl _ _ => False
                   | _ => True
                   end) ll.

Lemma historyOf_nil:
  forall ll,
    historyOf ll = nil <-> NonActive ll.
Proof.
  unfold NonActive; intros; split.
  - induction ll; intros; [auto|].
    destruct a; simpl in H; [auto|auto|discriminate].
  - induction ll; intros; [auto|].
    inv H.
    destruct a; simpl in *; intuition auto.
Qed.

Lemma historyOf_app:
  forall ll hst1 hst2,
    historyOf ll = hst1 ++ hst2 ->
    exists ll1 ll2,
      ll = ll1 ++ ll2 /\ historyOf ll1 = hst1 /\ historyOf ll2 = hst2.
Proof.
  induction ll; simpl; intros.
  - apply eq_sym, app_eq_nil in H; dest; subst.
    do 2 (exists nil); auto.
  - destruct a; simpl in *.
    + specialize (IHll _ _ H); dest; subst.
      eexists (_ :: _), _; repeat split.
    + specialize (IHll _ _ H); dest; subst.
      eexists (_ :: _), _; repeat split.
    + destruct hst1 as [|hst1].
      * simpl in H; subst.
        exists nil; eexists; repeat split.
      * simpl in H; inv H.
        specialize (IHll _ _ H2); dest; subst.
        eexists (_ :: _), _; repeat split.
Qed.

Lemma nonActive_transactional:
  forall sys ll,
    NonActive ll -> Transactional sys (historyOf ll).
Proof.
  intros.
  apply historyOf_nil in H.
  rewrite H.
  left; reflexivity.
Qed.

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

Lemma transactional_cons_inv:
  forall sys a ll,
    Transactional sys (a :: ll) ->
    Transactional sys ll.
Proof.
  unfold Transactional; intros.
  destruct H; [discriminate|].
  destruct H as [pmin [pmouts [? ?]]].
  remember (a :: ll) as all; inv H0; [inv H3; auto|].
  inv H4.
  right; eauto.
Qed.

Corollary transactional_ocons_inv:
  forall sys oa ll,
    Transactional sys (oa ::> ll) ->
    Transactional sys ll.
Proof.
  destruct oa as [a|]; simpl; intros; auto.
  eauto using transactional_cons_inv.
Qed.

Lemma step_seq_ins:
  forall sys ins st1 st2,
    step_mod sys st1 (LblIns ins) st2 ->
    forall ast1,
      atm2State ast1 = st1 ->
      exists ast2,
        atm2State ast2 = st2 /\
        step_seq sys ast1 (LblIns ins) ast2.
Proof.
  intros; subst.
  apply step_mod_step_det in H.
  inv H.

  exists {| st_oss := st_oss ast1;
            st_msgs := distributeMsgs (toAtomicMsgsF ins) (st_msgs ast1) |}.
  split.
  - unfold atm2State; simpl.
    f_equal.

    clear.
    induction ins; [reflexivity|].
    simpl; rewrite <-IHins; clear.
    remember (distributeMsgs (toAtomicMsgsF ins) (st_msgs ast1)) as msgs; clear Heqmsgs.
    admit. (* trivial but very tedious *)
    
  - destruct ast1 as [oss1 msgs1]; simpl.
    econstructor; eauto.
Admitted.

Lemma transactional_steps_seq:
  forall sys ll,
    Transactional sys (historyOf ll) ->
    forall st1 st2,
      steps step_mod sys st1 ll st2 ->
      forall ast1,
        atm2State ast1 = st1 ->
        exists ast2,
          atm2State ast2 = st2 /\
          steps step_seq sys ast1 ll ast2.
Proof.
  induction ll as [|l ll]; simpl; intros; subst;
    [inv H0; eexists; repeat split; constructor|].

  (* NOTE: [l] is the youngest label. *)
  inv H0.
  specialize (IHll (transactional_ocons_inv _ _ H) _ _ H4 _ eq_refl).
  destruct IHll as [past2 [? ?]]; subst.
  destruct l; simpl in H.

  - (* LblEmpty *)
    apply step_mod_step_det in H6; inv H6.
    eexists; repeat split.
    econstructor; eauto.
    econstructor.

  - (* LblIns *)
    eapply step_seq_ins in H6; [|reflexivity].
    destruct H6 as [ast2 [? ?]]; subst.
    eexists; repeat split.
    econstructor; eauto.
    
  - (* LblHdl *)
    admit.
    (* eexists; split; [|econstructor; [eassumption|]]. *)

Admitted.

Corollary nonActive_steps_seq:
  forall ll,
    NonActive ll ->
    forall sys st1 st2,
      steps step_mod sys st1 ll st2 ->
      forall ast1,
        atm2State ast1 = st1 ->
        exists ast2,
          atm2State ast2 = st2 /\
          steps step_seq sys ast1 ll ast2.
Proof.
  intros.
  apply nonActive_transactional with (sys:= sys) in H.
  eauto using transactional_steps_seq.
Qed.

Lemma sequential_steps':
  forall sys trs,
    Forall (Transactional sys) trs ->
    forall ll,
      historyOf ll = concat trs ->
      forall st,
        steps step_mod sys (getStateInit sys) ll st ->
        exists ast,
          atm2State ast = st /\
          steps step_seq sys (getStateInit sys) ll ast.
Proof.
  induction trs; intros.

  - simpl in H0; apply historyOf_nil in H0.
    eapply nonActive_steps_seq; eauto.
    unfold atm2State, atm2M, getStateInit; simpl.
    mred.

  - inv H.
    specialize (IHtrs H5); clear H5.

    simpl in H0.
    apply historyOf_app in H0.
    destruct H0 as [ll2 [ll1 [? [? ?]]]]; subst.

    eapply steps_split in H1; [|reflexivity].
    destruct H1 as [sti [? ?]].
    specialize (IHtrs _ H2 _ H); clear H H2.
    destruct IHtrs as [past [? ?]]; subst.

    pose proof (transactional_steps_seq H4 H0 eq_refl) as Hseq2.
    destruct Hseq2 as [ast2 [? ?]]; subst.

    eexists; split; [reflexivity|].
    eauto using steps_append.
Qed.

Lemma sequential_steps:
  forall sys ll,
    Sequential sys (historyOf ll) ->
    forall st,
      steps step_mod sys (getStateInit sys) ll st ->
      exists ast,
        atm2State ast = st /\
        steps step_seq sys (getStateInit sys) ll ast.
Proof.
  unfold Sequential; intros.
  destruct H as [trs [? ?]].
  eauto using sequential_steps'.
Qed.

Theorem serializable_step_seq:
  forall sys ll st,
    steps step_mod sys (getStateInit sys) ll st ->
    Serializable sys step_mod ll ->
    Behavior step_seq sys (behaviorOf ll).
Proof.
  unfold Serializable; intros.
  destruct H0 as [sll [sst [? [? ?]]]].

  pose proof (equiv_history_behavior H H0 H2) as Hnll.
  destruct Hnll as [nll [? [? ?]]].

  rewrite <-H4 in H1.
  pose proof (sequential_steps H1 H3) as Hseq.
  destruct Hseq as [ast [? ?]]; subst.

  eapply Behv; eauto.
Qed.

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

