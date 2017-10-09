Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common ListSupport FMap Syntax Semantics SemFacts SemDet SemSeq Serial.

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

Lemma atm2Q_enq_comm:
  forall am aa q,
    atm2Q (enq {| atm_msg := am; atm_active := aa |} q) =
    enq am (atm2Q q).
Proof.
  unfold atm2Q, enq; intros.
  apply map_app.
Qed.

Lemma atm2Q_find:
  forall chn cs,
    (M.map atm2Q cs)@[chn] = cs@[chn] >>= (fun q => Some (atm2Q q)).
Proof.
  intros; rewrite M.F.P.F.map_o; reflexivity.
Qed.

Lemma atm2C_enqC_comm:
  forall am aa chn cs,
    atm2C (enqC chn {| atm_msg := am; atm_active := aa |} cs) =
    enqC chn am (atm2C cs).
Proof.
  unfold atm2C, enqC; intros.
  rewrite atm2Q_find.
  destruct (cs@[chn]); simpl;
    try (rewrite M.map_add, atm2Q_enq_comm; reflexivity).
Qed.

Lemma atm2C_find:
  forall from mf,
    (M.map atm2C mf)@[from] = mf@[from] >>= (fun cs => Some (atm2C cs)).
Proof.
  intros; rewrite M.F.P.F.map_o; reflexivity.
Qed.

Lemma atm2MF_enqMF_comm:
  forall am aa from chn mf,
    atm2MF (enqMF from chn {| atm_msg := am; atm_active := aa |} mf) =
    enqMF from chn am (atm2MF mf).
Proof.
  unfold atm2MF, enqMF; intros.
  rewrite atm2C_find.
  destruct (mf@[from]); simpl.
  - rewrite M.map_add, atm2C_enqC_comm; reflexivity.
  - rewrite M.map_add, atm2C_enqC_comm.
    unfold atm2C; rewrite M.map_empty; reflexivity.
Qed.

Lemma atm2MF_find:
  forall to msgs,
    (M.map atm2MF msgs)@[to] = msgs@[to] >>= (fun mf => Some (atm2MF mf)).
Proof.
  intros; rewrite M.F.P.F.map_o; reflexivity.
Qed.

Lemma atm2M_distributeMsg_comm:
  forall am aa msgs,
    atm2M (distributeMsg {| atm_msg := am; atm_active := aa |} msgs) =
    distributeMsg am (atm2M msgs).
Proof.
  destruct am as [[mty mfr mto mch] mv]; intros.
  unfold atm2M, distributeMsg, enqM; simpl.
  rewrite atm2MF_find.
  destruct (msgs@[mto]); simpl.
  - rewrite M.map_add, atm2MF_enqMF_comm; reflexivity.
  - rewrite M.map_add, atm2MF_enqMF_comm.
    unfold atm2MF; rewrite M.map_empty; reflexivity.
Qed.

Lemma atm2M_distributeMsgs_comm:
  forall ins msgs,
    atm2M (distributeMsgs (toAtomicMsgsF ins) msgs) =
    distributeMsgs ins (atm2M msgs).
Proof.
  induction ins; intros; [reflexivity|].
  simpl; rewrite <-IHins.
  apply atm2M_distributeMsg_comm.
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
    rewrite atm2M_distributeMsgs_comm.
    reflexivity.
  - destruct ast1 as [oss1 msgs1]; simpl.
    econstructor; eauto.
Qed.

Lemma atomic_mouts_internal:
  forall sys st1 ll st2,
    steps step_mod sys st1 ll st2 ->
    forall min mouts,
      Atomic min (historyOf ll) mouts ->
      Forall (fun m => isInternal sys (mid_from (msg_id m)) = true) mouts.
Proof.
  induction 1; simpl; intros; [inv H|].

  destruct lbl; eauto.

  simpl in H1; inv H1.
  - inv H6.
    apply step_mod_outs_internal in H0; auto.
  - apply Forall_app.
    + apply Forall_remove; eauto.
    + apply step_mod_outs_internal in H0; auto.
Qed.

Lemma atomic_internals:
  forall sys min mouts hll,
    Atomic min hll mouts ->
    forall ll st1 st2,
      hll = historyOf ll ->
      steps step_mod sys st1 ll st2 ->
      Forall (fun hl => isInternal sys (mid_from (msg_id (hlbl_hdl hl))) = true)
             (tl (rev hll)).
Proof.
  induction 1; simpl; intros; subst; [constructor|].

  destruct hst as [|hl hst]; [constructor|].
  rewrite tl_app by (simpl; destruct (rev hst); discriminate).

  rewrite cons_app in H1.
  apply eq_sym, historyOf_app in H1.
  destruct H1 as [ll1 [ll2 [? [? ?]]]]; subst.

  eapply steps_split in H2; [|reflexivity].
  destruct H2 as [sti [? ?]].

  apply Forall_app; eauto.

  clear IHAtomic.
  repeat constructor.
  simpl.
  rewrite <-H4 in H.
  eapply atomic_mouts_internal in H1; [|eassumption].
  eapply Forall_forall in H1; eauto.
Qed.

Lemma step_seq_hdl:
  forall sys hdl outs ll,
    Transactional sys ({| hlbl_hdl := hdl; hlbl_outs := outs |} :: historyOf ll) ->
    forall ast1 ast2 st1 st2 st3,
      atm2State ast1 = st1 ->
      atm2State ast2 = st2 ->
      steps step_mod sys st1 ll st2 ->
      steps step_seq sys ast1 ll ast2 ->
      step_mod sys st2 (LblHdl hdl outs) st3 ->
      exists ast3,
        atm2State ast3 = st3 /\
        step_seq sys ast2 (LblHdl hdl outs) ast3.
Proof.
  intros; subst.
  inv H; [discriminate|].
  destruct H0 as [min [mouts [? ?]]].

  destruct ast2 as [oss2 amsgs2].
  apply step_mod_step_det in H4; inv H4.

  inv H0.
  - admit.
  - exists {| st_oss := oss2 +[obj_idx obj <- pos];
              st_msgs := distributeMsgs
                           (toAtomicMsgsF (intOuts sys (pmsg_outs fpmsg os (msg_value hdl))))
                           (if isExternal sys fidx then deactivateM amsgs2 else amsgs2) |}.
    split.
    + unfold atm2State; simpl.
      rewrite <-atm2M_distributeMsgs_comm.
      eapply atomic_mouts_internal in H9; [|eassumption].
      eapply Forall_forall in H9; [|eassumption].
      destruct H14 as [? [? ?]]; subst.
      apply internal_not_external in H9; rewrite H9.
      reflexivity.
    + change hdl with (getMsg {| atm_msg := hdl; atm_active := true |}).
      eapply SsInt; try reflexivity; try eassumption; eauto.
      * admit.
      * admit.
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
    eapply step_seq_hdl in H; eauto.
    destruct H as [ast3 [? ?]]; subst.
    eexists; repeat split.
    econstructor; eauto.
Qed.

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

