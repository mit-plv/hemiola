Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepT SemFacts.
Require Import Simulation Serial SerialFacts Invariant.

Require Import Omega.

Set Implicit Arguments.

Section TrsSim.
  Variables (sim: TState -> TState -> Prop)
            (ginv: TState -> Prop).

  Local Infix "≈" := sim (at level 30).

  Variables (impl spec: System).

  Definition TrsSimInit := sim (initsOf impl) (initsOf spec).
 
  Definition TrsSimulates :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall ihst ist2,
        trsStepsT impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps step_t spec sst1 shst sst2 /\
          behaviorOf impl ihst = behaviorOf spec shst /\
          ist2 ≈ sst2.

  Hypotheses
    (Hsimi: TrsSimInit)
    (Hsim: TrsSimulates)
    (Hginvi: InvInit impl ginv)
    (Hginv: InvStep impl step_t ginv).

  Lemma trs_simulation_steps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall trss ihst ist2,
        Forall (Transactional impl) trss ->
        ihst = List.concat trss ->
        steps step_t impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps step_t spec sst1 shst sst2 /\
          behaviorOf impl ihst = behaviorOf spec shst /\
          ist2 ≈ sst2 /\ ginv ist2.
  Proof.
    induction trss as [|trs trss]; simpl; intros; subst.
    - inv H3; exists sst1, nil; repeat split.
      + constructor.
      + assumption.
      + assumption.
    - inv H1.
      eapply steps_split in H3; [|reflexivity].
      destruct H3 as [sti [? ?]].
      specialize (IHtrss _ _ H6 eq_refl H1).
      destruct IHtrss as [isst [ishst [? [? [? ?]]]]].
      pose proof (Hsim H7 H8 (conj H2 H5)); destruct H9 as [sst2 [shst [? [? ?]]]].

      pose proof (inv_steps Hginv H8 H2).
      do 2 eexists; repeat split.
      + eapply steps_append; eauto.
      + do 2 rewrite behaviorOf_app.
        rewrite H4, H10; reflexivity.
      + assumption.
      + assumption.
  Qed.

  Corollary simulation_seqSteps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
       ginv ist1 ->
      forall ihst ist2,
        seqStepsT impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps step_t spec sst1 shst sst2 /\
          behaviorOf impl ihst = behaviorOf spec shst /\
          ist2 ≈ sst2 /\ ginv ist2.
  Proof.
    unfold seqStepsT, seqSteps, Sequential; intros; dest; subst.
    eapply trs_simulation_steps; eauto.
  Qed.

  Theorem sequential_simulation_implies_refinement:
    seqStepsT # steps step_t |-- impl ⊑ spec.
  Proof.
    unfold Simulates, Refines; intros.
    inv H.
    eapply simulation_seqSteps in H0; [|exact Hsimi|exact Hginvi].
    destruct H0 as [sst2 [shst [? [? [? ?]]]]].
    econstructor; eauto.
  Qed.

End TrsSim.

Section TrsSimSep.
  Variables (sim: TState -> TState -> Prop)
            (ginv: TState -> Prop).

  Local Infix "≈" := sim (at level 30).

  Variables (impl spec: System).

  Definition TrsSimSilent :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall ist2,
        step_t impl ist1 (emptyRLabel _) ist2 ->
        exists sst2,
          step_t spec sst1 (emptyRLabel _) sst2 /\
          ist2 ≈ sst2.

  Definition TrsSimIns :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall imins ist2,
        step_t impl ist1 (RlblIns imins) ist2 ->
        exists sst2,
          step_t spec sst1 (RlblIns imins) sst2 /\
          ist2 ≈ sst2.

  Definition TrsSimOuts :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall imouts ist2,
        step_t impl ist1 (RlblOuts imouts) ist2 ->
        exists sst2,
          step_t spec sst1 (RlblOuts imouts) sst2 /\
          ist2 ≈ sst2.

  Definition TrsSimAtomic rq :=
    forall hst mouts,
      ExtAtomic impl rq hst mouts ->
      forall ist1,
        ginv ist1 ->
        forall sst1,
          ist1 ≈ sst1 ->
          forall ist2,
            steps step_t impl ist1 hst ist2 ->
            exists sst2 shst,
              steps step_t spec sst1 shst sst2 /\
              behaviorOf impl hst = behaviorOf spec shst /\
              ist2 ≈ sst2.

  Hypotheses
    (Hsimi: TrsSimInit sim impl spec)
    (HsimSlt: TrsSimSilent)
    (HsimIns: TrsSimIns)
    (HsimOuts: TrsSimOuts)
    (HsimAtm: forall rq, TrsSimAtomic rq).

  Lemma trs_sim_step_steps_trs:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall ihst ist2,
        Transactional impl ihst ->
        steps step_t impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps step_t spec sst1 shst sst2 /\
          behaviorOf impl ihst = behaviorOf spec shst /\
          ist2 ≈ sst2.
  Proof.
    destruct 3; simpl; intros; subst.
    - inv H1; inv H5.
      eapply HsimSlt in H7; eauto.
      destruct H7 as [sst2 [? ?]].
      eexists; eexists (_ :: _); repeat split.
      + econstructor; [econstructor|eassumption].
      + reflexivity.
      + assumption.
    - inv H2; inv H5.
      eapply HsimIns in H7; eauto.
      destruct H7 as [sst2 [? ?]].
      eexists; eexists (_ :: _); repeat split.
      + econstructor; [econstructor|eassumption].
      + reflexivity.
      + assumption.
    - inv H2; inv H5.
      eapply HsimOuts in H7; eauto.
      destruct H7 as [sst2 [? ?]].
      eexists; eexists (_ :: _); repeat split.
      + econstructor; [econstructor|eassumption].
      + reflexivity.
      + assumption.
    - pose proof (HsimAtm H1 H0 H H2).
      dest; eauto.
  Qed.

  Lemma trs_sim_in_atm_simulates:
    TrsSimulates sim ginv impl spec.
  Proof.
    unfold TrsSimulates; intros.
    destruct H1.
    eapply trs_sim_step_steps_trs in H2; eauto.
  Qed.

End TrsSimSep.

Lemma InvSim_implies_TrsSimulates:
  forall sim ginv impl spec,
    InvStep impl step_t ginv ->
    InvSim step_t step_t ginv sim impl spec ->
    TrsSimulates sim ginv impl spec.
Proof.
  unfold TrsSimulates; intros.
  inv H3.
  eapply inv_simulation_steps; eauto.
Qed.

Lemma TrsSimulates_no_rules:
  forall sim ginv impl spec,
    merqsOf impl = merqsOf spec ->
    merssOf impl = merssOf spec ->
    InvStep impl step_t ginv ->
    (ginv ->i ValidTrss impl) ->
    MsgsSim sim ->
    ImpliesSimMP sim ->
    sys_rules impl = nil ->
    TrsSimulates sim ginv impl spec.
Proof.
  intros; hnf; intros.
  eapply InvSim_implies_TrsSimulates; eauto.
  eapply steps_simulation_ValidTrss_SimMP_no_rules; eauto.
Qed.

Section TrsPreserving.

  Definition trsPreservingRule (rule: Rule) :=
    exists tid,
      Forall (fun mid => mid = tid) (rule_msg_ids rule) /\
      forall post porq ins nost norq outs,
        rule_postcond rule post porq ins nost norq outs ->
        Forall (fun idm => msg_id (valOf idm) = tid) outs.

  Definition trsPreservingSys (sys: System) :=
    Forall trsPreservingRule (sys_rules sys).

End TrsPreserving.

Section TrsDisj.

  Definition TrsDisj (rules1 rules2: list Rule) :=
    forall rule1 rule2,
      In rule1 rules1 ->
      In rule2 rules2 ->
      forall tid1 tid2,
        In tid1 (rule_msg_ids rule1) ->
        In tid2 (rule_msg_ids rule2) ->
        tid1 <> tid2.

  Definition TrsDisjSys (sys1 sys2: System) :=
    TrsDisj (sys_rules sys1) (sys_rules sys2).

  Lemma TrsDisj_sym:
    forall ms1 ms2,
      TrsDisj ms1 ms2 ->
      TrsDisj ms2 ms1.
  Proof.
    unfold TrsDisj; intros.
    specialize (H _ _ H1 H0 _ _ H3 H2).
    auto.
  Qed.

  Lemma TrsDisj_SubList_1:
    forall ms1 ms2,
      TrsDisj ms1 ms2 ->
      forall ms3,
        SubList ms3 ms1 ->
        TrsDisj ms3 ms2.
  Proof.
    unfold TrsDisj; intros.
    specialize (H0 _ H1).
    specialize (H _ _ H0 H2).
    auto.
  Qed.

  Lemma TrsDisj_SubList_2:
    forall ms1 ms2,
      TrsDisj ms1 ms2 ->
      forall ms3,
        SubList ms3 ms2 ->
        TrsDisj ms1 ms3.
  Proof.
    unfold TrsDisj; intros.
    specialize (H0 _ H2).
    specialize (H _ _ H1 H0).
    auto.
  Qed.

End TrsDisj.

Lemma trsPreservingSys_ins_outs_same_tid:
  forall sys,
    trsPreservingSys sys ->
    forall st1 st2 orule hins houts,
      step_t sys st1 (RlblInt orule hins houts) st2 ->
      exists tid,
        Forall (fun idm => msg_id (getMsg (valOf idm)) = tid) hins /\
        Forall (fun idm => msg_id (getMsg (valOf idm)) = tid) houts.
Proof.
  intros; inv H0; [(* anything *) exists 0; split; constructor|].
  unfold trsPreservingSys in H.
  eapply Forall_forall in H; eauto.
  unfold trsPreservingRule in H.
  destruct H as [tid [? ?]].
  specialize (H0 _ _ _ _ _ _ H14).
  exists tid; split; auto.
  - rewrite <-H11 in H.
    clear -H; induction hins; [constructor|].
    inv H; constructor; auto.
  - clear -H0; induction outs; [constructor|].
    inv H0; constructor; auto.
Qed.

Lemma trsPreservineSys_atomic_same_tid:
  forall sys,
    trsPreservingSys sys ->
    forall rq (hst: THistory) mouts,
      ExtAtomic sys rq hst mouts ->
      forall mtid,
        mtid = msg_id (getMsg (valOf rq)) ->
        forall ist1 ist2,
          steps step_t sys ist1 hst ist2 ->
          ForallMP (fun _ msg => msg_id (getMsg msg) = mtid) mouts /\
          Forall (fun tl =>
                    match tl with
                    | RlblInt _ ins _ =>
                      Forall (fun msg => msg_id (getMsg (valOf msg)) = mtid) ins
                    | _ => False
                    end) hst.
Proof.
  inversion_clear 2.
  induction H2; simpl; intros.
  - subst; constructor; auto.
    inv H2.
    eapply trsPreservingSys_ins_outs_same_tid in H7; eauto.
    destruct H7 as [tid [? ?]].
    apply ForallMP_enqMsgs.
    + apply ForallMP_emptyMP.
    + inv H0; inv H2; auto.
  - subst; inv H5.
    specialize (IHAtomic H1 _ eq_refl _ _ H8); dest.
    split.
    + apply ForallMP_enqMsgs.
      * apply ForallMP_deqMsgs; assumption.
      * eapply ForallMP_Forall_InMP in H3; eauto.
        eapply trsPreservingSys_ins_outs_same_tid in H10; eauto.
        destruct H10 as [tid [? ?]].
        destruct msgs; [elim H0; reflexivity|].
        inv H6; inv H3.
        simpl in H10; rewrite <-H10; auto.
    + constructor; auto.
      eapply ForallMP_Forall_InMP in H3; eauto.
      simpl in H3; auto.
Qed.

Lemma rule_mids_tid_In:
  forall tid (rules: list Rule) r,
    In tid (rule_msg_ids r) ->
    In r rules ->
    In tid (List.concat (map (rule_msg_ids) rules)).
Proof.
  induction rules; simpl; intros; auto.
  destruct H0; subst.
  - apply in_or_app; left; assumption.
  - apply in_or_app; right; eauto.
Qed.

Section Compositionality.

  Variables (impl1 impl2 spec: System).
  Hypotheses
    (Hoinds: oindsOf impl1 = oindsOf impl2)
    (Hminds: mindsOf impl1 = mindsOf impl2)
    (Hmerqs: merqsOf impl1 = merqsOf impl2)
    (Hmerss: merssOf impl1 = merssOf impl2)
    (Hmt1: trsPreservingSys impl1)
    (Hmt2: trsPreservingSys impl2)
    (Hmtdisj: TrsDisjSys impl1 impl2).

  Variable (impl: System).
  Hypotheses
    (Hmt: trsPreservingSys impl)
    (Hii: oindsOf impl = oindsOf impl1)
    (Hmm: mindsOf impl = mindsOf impl1)
    (Hqq: merqsOf impl = merqsOf impl1)
    (Hss: merssOf impl = merssOf impl1)
    (Himpl:
       forall rule,
         In rule (sys_rules impl) ->
         In rule (sys_rules impl1 ++ sys_rules impl2)).

  Variables (ginv: TState -> Prop)
            (simR: TState -> TState -> Prop).
  
  Local Infix "≈" := simR (at level 30).
  
  Hypotheses (Hinv1: InvStep impl1 step_t ginv)
             (Hinv2: InvStep impl2 step_t ginv).

  Lemma invariant_compositional:
    InvStep impl step_t ginv.
  Proof.
    unfold InvStep; intros.
    inv H0.
    - assumption.
    - eapply Hinv1; eauto.
      eapply StIns; try reflexivity; try assumption.
      eapply ValidMsgsExtIn_merqsOf; eauto.
    - eapply Hinv1; eauto.
      eapply StOuts; try reflexivity; try assumption.
      eapply ValidMsgsExtOut_merssOf; eauto.
    - specialize (Himpl _ H9).
      apply in_app_or in Himpl; destruct Himpl.
      + eapply Hinv1; eauto.
        eapply StInt; try reflexivity; try eassumption.
        * rewrite <-Hii; assumption.
        * eapply ValidMsgsIn_mindsOf; eauto.
        * eapply ValidMsgsOut_mindsOf_merssOf; eauto.
        * rewrite Hss; reflexivity.
      + eapply Hinv2; eauto.
        eapply StInt; try reflexivity; try eassumption.
        * rewrite <-Hoinds, <-Hii; assumption.
        * eapply ValidMsgsIn_mindsOf; eauto.
          rewrite <-Hminds; auto.
        * eapply ValidMsgsOut_mindsOf_merssOf; eauto.
          { rewrite <-Hminds; auto. }
          { rewrite <-Hmerss; auto. }
        * rewrite Hss, Hmerss; reflexivity.
  Qed.

  Lemma TrsDisjSys_distr_same_tid:
    forall mtid,
      (forall rule,
          rule_msg_ids rule <> nil ->
          Forall (fun mid => mid = mtid) (rule_msg_ids rule) ->
          In rule (sys_rules impl) ->
          In rule (sys_rules impl1)) \/
      (forall rule,
          rule_msg_ids rule <> nil ->
          Forall (fun mid => mid = mtid) (rule_msg_ids rule) ->
          In rule (sys_rules impl) ->
          In rule (sys_rules impl2)).
  Proof.
    intros.
    destruct (mtid ?<n List.concat (map (fun rule => rule_msg_ids rule)
                                        (sys_rules impl1))).
    - left; intros.
      pose proof (Himpl _ H1).
      apply in_app_or in H2; destruct H2; [assumption|].
      exfalso.
      assert (exists mrule, In mtid (rule_msg_ids mrule) /\
                            In mrule (sys_rules impl1)).
      { clear -i.
        induction (sys_rules impl1); [inv i|].
        simpl in i; apply in_app_or in i; destruct i.
        { exists a; split; intuition. }
        { specialize (IHl H); dest.
          eexists; repeat split; eauto.
          right; auto.
        }
      }
      assert (In mtid (rule_msg_ids rule)).
      { clear -H H0; destruct (rule_msg_ids rule); [elim H; reflexivity|].
        inv H0; left; reflexivity.
      }
      destruct H3 as [mrule [? ?]].
      specialize (Hmtdisj _ _ H5 H2 H3 H4).
      elim Hmtdisj; reflexivity.
      
    - right; intros.
      pose proof (Himpl _ H1).
      apply in_app_or in H2; destruct H2; [|assumption].
      elim n; clear n.
      eapply rule_mids_tid_In; eauto.
      clear -H H0; destruct (rule_msg_ids rule); [elim H; reflexivity|].
      inv H0; left; reflexivity.
  Qed.

  Lemma atomic_steps_compositional:
    forall ist1 hst ist2,
      steps step_t impl ist1 hst ist2 ->
      forall rq mouts,
        ExtAtomic impl rq hst mouts ->
        steps step_t impl1 ist1 hst ist2 \/
        steps step_t impl2 ist1 hst ist2.
  Proof.
    intros.
    pose proof (TrsDisjSys_distr_same_tid (msg_id (getMsg (valOf rq)))).
    pose proof (trsPreservineSys_atomic_same_tid Hmt H0 eq_refl H).
    destruct H2 as [_ ?].
    destruct H1.

    - left.
      generalize dependent ist2.
      inv H0; induction H3; intros.
      + inv H0; inv H6; inv H8.
        econstructor; [econstructor|].
        assert (rule_msg_ids rqr <> nil) by (rewrite <-H13; discriminate).
        assert (Forall (fun mid => mid = msg_id (getMsg (valOf rq))) (rule_msg_ids rqr))
          by (rewrite <-H13; constructor; auto).
        econstructor; eauto.
        * rewrite <-Hii; auto.
        * eapply ValidMsgsIn_mindsOf; eauto.
        * eapply ValidMsgsOut_mindsOf_merssOf; eauto.
        * rewrite Hss; reflexivity.
      + inv H2; inv H5.
        specialize (IHAtomic H1 H9 H _ H10).
        econstructor; eauto.
        inv H12.
        assert (rule_msg_ids rule <> nil).
        { rewrite <-H18; clear -H0.
          destruct msgs; [elim H0; reflexivity|discriminate].
        }
        assert (Forall (fun mid => mid = msg_id (getMsg (valOf rq))) (rule_msg_ids rule)).
        { rewrite <-H18.
          clear -H8; induction msgs; [constructor|].
          inv H8; constructor; auto.
        }
        econstructor; eauto.
        * rewrite <-Hii; auto.
        * eapply ValidMsgsIn_mindsOf; eauto.
        * eapply ValidMsgsOut_mindsOf_merssOf; eauto.
        * rewrite Hss; reflexivity.

    - right.
      generalize dependent ist2.
      inv H0; induction H3; intros.
      + inv H0; inv H6; inv H8.
        econstructor; [econstructor|].
        assert (rule_msg_ids rqr <> nil) by (rewrite <-H13; discriminate).
        assert (Forall (fun mid => mid = msg_id (getMsg (valOf rq))) (rule_msg_ids rqr))
          by (rewrite <-H13; constructor; auto).
        econstructor; eauto.
        * rewrite <-Hoinds, <-Hii; auto.
        * eapply ValidMsgsIn_mindsOf; eauto.
          rewrite <-Hminds; auto.
        * eapply ValidMsgsOut_mindsOf_merssOf; eauto.
          { rewrite <-Hminds; auto. }
          { rewrite <-Hmerss; auto. }
        * rewrite <-Hmerss, <-Hss; reflexivity.
      + inv H2; inv H5.
        specialize (IHAtomic H1 H9 H _ H10).
        econstructor; eauto.
        inv H12.
        assert (rule_msg_ids rule <> nil).
        { rewrite <-H18; clear -H0.
          destruct msgs; [elim H0; reflexivity|discriminate].
        }
        assert (Forall (fun mid => mid = msg_id (getMsg (valOf rq))) (rule_msg_ids rule)).
        { rewrite <-H18.
          clear -H8; induction msgs; [constructor|].
          inv H8; constructor; auto.
        }
        econstructor; eauto.
        * rewrite <-Hoinds, <-Hii; auto.
        * eapply ValidMsgsIn_mindsOf; eauto.
          rewrite <-Hminds; auto.
        * eapply ValidMsgsOut_mindsOf_merssOf; eauto.
          { rewrite <-Hminds; auto. }
          { rewrite <-Hmerss; auto. }
        * rewrite <-Hmerss, <-Hss; reflexivity.
  Qed.

  Hypotheses (Hsim1: TrsSimulates simR ginv impl1 spec)
             (Hsim2: TrsSimulates simR ginv impl2 spec).

  Lemma trsSimulates_transactional_compositional:
    forall ihst,
      Transactional impl ihst ->
      forall ist1 sst1,
        ist1 ≈ sst1 ->
        ginv ist1 ->
        forall ist2,
          steps step_t impl ist1 ihst ist2 ->
          exists (sst2 : TState) (shst : list TLabel),
            steps step_t spec sst1 shst sst2 /\
            behaviorOf impl ihst = behaviorOf spec shst /\
            ist2 ≈ sst2.
  Proof.
    destruct 1; simpl; intros; subst.

    - inv H1; inv H5; inv H7.
      exists sst1, nil; repeat split; [constructor|assumption].

    - assert (trsStepsT impl1 ist1 (RlblIns eins :: nil) ist2).
      { split; [|econstructor; reflexivity].
        econstructor; [econstructor|].
        inv H2; inv H5; inv H7.
        eapply StIns; try reflexivity; try assumption.
        eapply ValidMsgsExtIn_merqsOf; eauto.
      }
      exact (Hsim1 H0 H1 H).

    - assert (trsStepsT impl1 ist1 (RlblOuts eouts :: nil) ist2).
      { split; [|econstructor; reflexivity].
        econstructor; [econstructor|].
        inv H2; inv H5; inv H7.
        eapply StOuts; try reflexivity; try assumption.
        eapply ValidMsgsExtOut_merssOf; eauto.
      }
      exact (Hsim1 H0 H1 H).

    - pose proof (atomic_steps_compositional H2 H); destruct H3.
      + assert (Transactional impl1 hst).
        { econstructor; eauto.
          eapply extAtomic_preserved; eauto.
        }
        pose proof (Hsim1 H0 H1 (conj H3 H4)).
        rewrite behaviorOf_preserved with (impl4:= impl1) by assumption.
        assumption.
      + assert (Transactional impl2 hst).
        { econstructor; eauto.
          eapply extAtomic_preserved; eauto.
          rewrite Hqq; assumption.
        }
        pose proof (Hsim2 H0 H1 (conj H3 H4)).
        rewrite behaviorOf_preserved with (impl4:= impl2)
          by (rewrite Hii; assumption).
        assumption.
  Qed.

  Theorem trsSimulates_compositional: TrsSimulates simR ginv impl spec.
  Proof.
    unfold TrsSimulates, trsSteps in *; intros.
    destruct H1.
    eapply trsSimulates_transactional_compositional; eauto.
  Qed.

  Corollary trsSimulates_trsInvHolds_compositional:
    TrsSimulates simR ginv impl spec /\ InvStep impl step_t ginv.
  Proof.
    split.
    - apply trsSimulates_compositional.
    - apply invariant_compositional.
  Qed.

End Compositionality.

