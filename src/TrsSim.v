Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepT SemFacts.
Require Import Simulation Serial SerialFacts Invariant.

Require Import Omega.

Set Implicit Arguments.

Section TrsSim.
  Variables (sim: TState -> TState -> Prop)
            (ginv: TState -> Prop)
            (p: Label -> Label).

  Local Infix "≈" := sim (at level 30).

  Variables (impl spec: System).

  Definition TrsSimInit := sim (initsOf impl) (initsOf spec).
 
  Definition TrsSimulates :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall ihst ist2,
        trsSteps impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps step_t spec sst1 shst sst2 /\
          map p (behaviorOf impl ihst) = behaviorOf spec shst /\
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
        ihst = concat trss ->
        steps step_t impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps step_t spec sst1 shst sst2 /\
          map p (behaviorOf impl ihst) = behaviorOf spec shst /\
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
        rewrite map_app.
        rewrite H4, H10; reflexivity.
      + assumption.
      + assumption.
  Qed.

  Corollary simulation_seqSteps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
       ginv ist1 ->
      forall ihst ist2,
        seqSteps impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps step_t spec sst1 shst sst2 /\
          map p (behaviorOf impl ihst) = behaviorOf spec shst /\
          ist2 ≈ sst2 /\ ginv ist2.
  Proof.
    unfold seqSteps, Sequential; intros; dest; subst.
    eapply trs_simulation_steps; eauto.
  Qed.

  Theorem sequential_simulation_implies_refinement:
    seqSteps # steps step_t |-- impl ⊑[p] spec.
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
            (ginv: TState -> Prop)
            (p: Label -> Label).

  Local Infix "≈" := sim (at level 30).

  Variables (impl spec: System).

  Definition TrsSimSilent :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall ist2,
        step_t impl ist1 emptyRLabel ist2 ->
        exists sst2,
          step_t spec sst1 emptyRLabel sst2 /\
          ist2 ≈ sst2.

  Definition TrsSimIn :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall imin ist2,
        step_t impl ist1 (RlblIn imin) ist2 ->
        exists smin sst2,
          step_t spec sst1 (RlblIn smin) sst2 /\
          extLabel spec (getLabel (RlblIn smin)) =
          Some (p (getLabel (RlblIn imin))) /\
          ist2 ≈ sst2.

  Definition TrsSimAtomic ts rq :=
    forall hst mouts,
      Atomic impl ts rq hst mouts ->
      forall ist1,
        ginv ist1 ->
        forall sst1,
          ist1 ≈ sst1 ->
          forall ist2,
            steps step_t impl ist1 hst ist2 ->
            exists sst2 shst,
              steps step_t spec sst1 shst sst2 /\
              map p (behaviorOf impl hst) = behaviorOf spec shst /\
              ist2 ≈ sst2.

  Hypotheses
    (Hsimi: TrsSimInit sim impl spec)
    (HsimSlt: TrsSimSilent)
    (HsimIn: TrsSimIn)
    (HsimAtm: forall ts rq, TrsSimAtomic ts rq).

  Lemma trs_sim_step_steps_trs:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall ihst ist2,
        Transactional impl ihst ->
        steps step_t impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps step_t spec sst1 shst sst2 /\
          map p (behaviorOf impl ihst) = behaviorOf spec shst /\
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
      eapply HsimIn in H7; eauto.
      destruct H7 as [smin [sst2 [? [? ?]]]].
      eexists; eexists (_ :: _); repeat split.
      + econstructor; [econstructor|eassumption].
      + simpl; simpl in H2; inv H2; reflexivity.
      + assumption.
    - pose proof (HsimAtm H1 H0 H H2).
      dest; eauto.
  Qed.

  Lemma trs_sim_in_atm_simulates:
    TrsSimulates sim ginv p impl spec.
  Proof.
    unfold TrsSimulates; intros.
    destruct H1.
    eapply trs_sim_step_steps_trs in H2; eauto.
  Qed.

End TrsSimSep.

Section TrsPreserving.

  Definition trsPreservingRule (rule: Rule) :=
    exists tid,
      Forall (fun mid => mid_tid mid = tid) (rule_mids rule) /\
      forall post porq ins nost norq outs,
        rule_postcond rule post porq ins nost norq outs ->
        Forall (fun mout => mid_tid (msg_id mout) = tid) outs.

  Definition trsPreservingSys (sys: System) :=
    Forall trsPreservingRule (sys_rules sys).

End TrsPreserving.

Section TrsDisj.

  Definition TrsDisj (rules1 rules2: list Rule) :=
    forall rule1 rule2,
      In rule1 rules1 ->
      In rule2 rules2 ->
      forall tid1 tid2,
        In tid1 (map mid_tid (rule_mids rule1)) ->
        In tid2 (map mid_tid (rule_mids rule2)) ->
        tid1 <> tid2.

  Definition TrsDisjSys (sys1 sys2: System) :=
    TrsDisj (rulesOf sys1) (rulesOf sys2).

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
      step_t sys st1 (RlblOuts orule hins houts) st2 ->
      exists tid,
        Forall (fun msg => mid_tid (msg_id (tmsg_msg msg)) = tid) hins /\
        Forall (fun msg => mid_tid (msg_id (tmsg_msg msg)) = tid) houts.
Proof.
  intros; inv H0; [(* anything *) exists 0; split; constructor|].
  unfold trsPreservingSys in H.
  eapply Forall_forall in H; eauto.
  unfold trsPreservingRule in H.
  destruct H as [tid [? ?]].
  specialize (H0 _ _ _ _ _ _ H12).
  exists tid; split; auto.
  - rewrite <-H9 in H.
    clear -H; induction hins; [constructor|].
    inv H; constructor; auto.
  - clear -H0; induction outs; [constructor|].
    inv H0; constructor; auto.
Qed.

Lemma trsPreservineSys_atomic_same_tid:
  forall sys,
    trsPreservingSys sys ->
    forall ts rq hst mouts,
      Atomic sys ts rq hst mouts ->
      forall mtid,
        mtid = mid_tid (msg_id rq) ->
        forall ist1 ist2,
          steps step_t sys ist1 hst ist2 ->
          Forall (fun msg => mid_tid (msg_id (getMsg msg)) = mtid) mouts /\
          Forall (fun tl =>
                    match tl with
                    | RlblIn msg => mid_tid (msg_id (getMsg msg)) = mtid
                    | RlblOuts _ ins _ =>
                      Forall (fun msg => mid_tid (msg_id (getMsg msg)) = mtid) ins
                    end) hst.
Proof.
  induction 2; simpl; intros.
  - subst; constructor; auto.
    inv H3.
    eapply trsPreservingSys_ins_outs_same_tid in H8; eauto.
    destruct H8 as [tid [? ?]].
    inv H2; auto.
  - subst; inv H4.
    specialize (IHAtomic _ eq_refl _ _ H7); dest.
    split.
    + apply Forall_app.
      * apply ForallMP_removeMsgs; assumption.
      * eapply ForallMP_SubList in H2; eauto.
        eapply trsPreservingSys_ins_outs_same_tid in H9; eauto.
        destruct H9 as [tid [? ?]].
        destruct msgs; [elim H1; reflexivity|].
        inv H5; inv H2.
        rewrite <-H9; auto.
    + constructor; auto.
      eapply ForallMP_SubList; eauto.
Qed.

Lemma rule_mids_tid_In:
  forall tid (rules: list Rule) r,
    In tid (map mid_tid (rule_mids r)) ->
    In r rules ->
    In tid (concat (map (fun rule => map mid_tid (rule_mids rule)) rules)).
Proof.
  induction rules; simpl; intros; auto.
  destruct H0; subst.
  - apply in_or_app; left; assumption.
  - apply in_or_app; right; eauto.
Qed.

Lemma steps_simulation_no_rules:
  forall (sim: TState -> TState -> Prop) msgF impl spec,
    ValidMsgMap msgF impl spec ->
    MsgInSim msgF sim ->
    sys_rules impl = nil ->
    forall ist1 sst1,
      sim ist1 sst1 ->
      forall ihst ist2,
        steps step_t impl ist1 ihst ist2 ->
        exists (sst2 : TState) (shst : list TLabel),
          steps step_t spec sst1 shst sst2 /\
          map (LabelMap msgF) (behaviorOf impl ihst) = behaviorOf spec shst /\ sim ist2 sst2.
Proof.
  induction 5; simpl; intros;
    [do 2 eexists; repeat split; [constructor|reflexivity|assumption]|].
  
  specialize (IHsteps H2); dest.
  inv H4.
  - do 2 eexists; repeat split; eauto.
  - destruct x as [noss norqs nmsgs ntid].
    do 2 eexists; repeat split.
    + eapply StepsCons.
      * eassumption.
      * eapply SdExt; try reflexivity.
        -- eapply validMsgMap_from_isExternal; eauto.
        -- eapply validMsgMap_to_isInternal; eauto.
    + simpl; rewrite <-H6; reflexivity.
    + apply H0; auto.
  - exfalso.
    rewrite H1 in H14; elim H14.
Qed.

Lemma TrsSimulates_no_rules:
  forall sim msgF ginv impl spec,
    ValidMsgMap msgF impl spec ->
    MsgInSim msgF sim ->
    sys_rules impl = nil ->
    TrsSimulates sim ginv (LabelMap msgF) impl spec.
Proof.
  intros; hnf; intros.
  inv H4.
  eapply steps_simulation_no_rules; eauto.
Qed.

Section Compositionality.

  Variables (impl1 impl2 spec: System).
  Hypotheses (Hidx: indicesOf impl1 = indicesOf impl2)
             (Hmt1: trsPreservingSys impl1)
             (Hmt2: trsPreservingSys impl2)
             (Hmtdisj: TrsDisjSys impl1 impl2).

  Variable (impl: System).
  Hypotheses (Hmt: trsPreservingSys impl)
             (Hii: indicesOf impl = indicesOf impl1)
             (Himpl:
                forall rule,
                  In rule (sys_rules impl) ->
                  In rule (sys_rules impl1 ++ sys_rules impl2)).

  Variables (ginv: TState -> Prop)
            (simR: TState -> TState -> Prop)
            (p: Label -> Label).
  
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
      econstructor; try reflexivity.
      + unfold fromExternal, isExternal in *; rewrite <-Hii; assumption.
      + unfold toInternal, isInternal in *; rewrite <-Hii; assumption.
    - specialize (Himpl _ H7).
      apply in_app_or in Himpl; destruct Himpl.
      + eapply Hinv1; eauto.
        eapply SdInt; try reflexivity; try eassumption.
        * rewrite <-Hii; assumption.
        * erewrite intOuts_same_indicesOf by eassumption.
          reflexivity.
      + eapply Hinv2; eauto.
        eapply SdInt; try reflexivity; try eassumption.
        * rewrite <-Hidx, <-Hii; assumption.
        * erewrite intOuts_same_indicesOf
            by (rewrite <-Hidx, <-Hii; reflexivity).
          reflexivity.
  Qed.

  Lemma TrsDisjSys_distr_same_tid:
    forall mtid,
      (forall rule,
          rule_mids rule <> nil ->
          Forall (fun mid => mid_tid mid = mtid) (rule_mids rule) ->
          In rule (sys_rules impl) ->
          In rule (sys_rules impl1)) \/
      (forall rule,
          rule_mids rule <> nil ->
          Forall (fun mid => mid_tid mid = mtid) (rule_mids rule) ->
          In rule (sys_rules impl) ->
          In rule (sys_rules impl2)).
  Proof.
    intros.
    destruct (mtid ?<n concat (map (fun rule => (map mid_tid (rule_mids rule)))
                                   (sys_rules impl1))).
    - left; intros.
      pose proof (Himpl _ H1).
      apply in_app_or in H2; destruct H2; [assumption|].
      exfalso.
      assert (exists mrule, In mtid (map mid_tid (rule_mids mrule)) /\
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
      assert (In mtid (map mid_tid (rule_mids rule))).
      { clear -H H0; destruct (rule_mids rule); [elim H; reflexivity|].
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
      clear -H H0; destruct (rule_mids rule); [elim H; reflexivity|].
      inv H0; left; reflexivity.
  Qed.

  Lemma atomic_steps_compositional:
    forall ist1 hst ist2,
      steps step_t impl ist1 hst ist2 ->
      forall ts rq mouts,
        Atomic impl ts rq hst mouts ->
        steps step_t impl1 ist1 hst ist2 \/
        steps step_t impl2 ist1 hst ist2.
  Proof.
    intros.
    pose proof (TrsDisjSys_distr_same_tid (mid_tid (msg_id rq))).
    pose proof (trsPreservineSys_atomic_same_tid Hmt H0 eq_refl H).
    destruct H2 as [_ ?].
    destruct H1.

    - left.
      generalize dependent ist2.
      induction H0; intros.
      + inv H3; inv H7; inv H9.
        econstructor; [econstructor|].
        rewrite intOuts_same_indicesOf with (sys2:= impl1) by assumption.
        assert (rule_mids rqr <> nil) by (rewrite <-H12; discriminate).
        assert (Forall (fun mid => mid_tid mid = mid_tid (msg_id rq)) (rule_mids rqr))
          by (rewrite <-H12; constructor; auto).
        econstructor; eauto.
        rewrite <-Hii; auto.
      + inv H2; inv H4.
        specialize (IHAtomic H1 H8 _ H9).
        econstructor; eauto.
        inv H11.
        rewrite intOuts_same_indicesOf with (sys2:= impl1) by assumption.
        assert (rule_mids rule <> nil).
        { rewrite <-H15; clear -H.
          destruct msgs; [elim H; reflexivity|discriminate].
        }
        assert (Forall (fun mid => mid_tid mid = mid_tid (msg_id rq)) (rule_mids rule)).
        { rewrite <-H15.
          clear -H7; induction msgs; [constructor|].
          inv H7; constructor; auto.
        }
        econstructor; eauto.
        rewrite <-Hii; auto.

    - right.
      assert (indicesOf impl = indicesOf impl2) as Hii2 by (rewrite Hii; auto).
      generalize dependent ist2.
      induction H0; intros.
      + inv H3; inv H7; inv H9.
        econstructor; [econstructor|].
        rewrite intOuts_same_indicesOf with (sys2:= impl2) by assumption.
        assert (rule_mids rqr <> nil) by (rewrite <-H12; discriminate).
        assert (Forall (fun mid => mid_tid mid = mid_tid (msg_id rq)) (rule_mids rqr))
          by (rewrite <-H12; constructor; auto).
        econstructor; eauto.
        rewrite <-Hii2; auto.
      + inv H2; inv H4.
        specialize (IHAtomic H1 H8 _ H9).
        econstructor; eauto.
        inv H11.
        rewrite intOuts_same_indicesOf with (sys2:= impl2) by assumption.
        assert (rule_mids rule <> nil).
        { rewrite <-H15; clear -H.
          destruct msgs; [elim H; reflexivity|discriminate].
        }
        assert (Forall (fun mid => mid_tid mid = mid_tid (msg_id rq)) (rule_mids rule)).
        { rewrite <-H15.
          clear -H7; induction msgs; [constructor|].
          inv H7; constructor; auto.
        }
        econstructor; eauto.
        rewrite <-Hii2; auto.
  Qed.

  Hypotheses (Hsim1: TrsSimulates simR ginv p impl1 spec)
             (Hsim2: TrsSimulates simR ginv p impl2 spec).

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
            map p (behaviorOf impl ihst) = behaviorOf spec shst /\
            ist2 ≈ sst2.
  Proof.
    destruct 1; simpl; intros; subst.

    - inv H1; inv H5; inv H7.
      exists sst1, nil; repeat split; [constructor|assumption].

    - assert (trsSteps impl1 ist1 (RlblIn msg :: nil) ist2).
      { split; [|econstructor; reflexivity].
        econstructor; [econstructor|].
        inv H2; inv H5; inv H7.
        eapply SdExt; try reflexivity.
        { unfold fromExternal, isExternal in *.
          rewrite Hii in H2; assumption.
        }
        { unfold toInternal, isInternal in *.
          rewrite Hii in H3; assumption.
        }
      }
      exact (Hsim1 H0 H1 H).
      
    - pose proof (atomic_steps_compositional H2 H); destruct H3.
      + assert (Transactional impl1 hst).
        { econstructor; eauto.
          eapply atomic_preserved; eauto.
        }
        pose proof (Hsim1 H0 H1 (conj H3 H4)).
        rewrite behaviorOf_preserved with (impl4:= impl1) by assumption.
        assumption.
      + assert (Transactional impl2 hst).
        { econstructor; eauto.
          eapply atomic_preserved; eauto.
          rewrite Hii; assumption.
        }
        pose proof (Hsim2 H0 H1 (conj H3 H4)).
        rewrite behaviorOf_preserved with (impl4:= impl2)
          by (rewrite Hii; assumption).
        assumption.
  Qed.

  Theorem trsSimulates_compositional: TrsSimulates simR ginv p impl spec.
  Proof.
    unfold TrsSimulates, trsSteps in *; intros.
    destruct H1.
    eapply trsSimulates_transactional_compositional; eauto.
  Qed.

  Corollary trsSimulates_trsInvHolds_compositional:
    TrsSimulates simR ginv p impl spec /\ InvStep impl step_t ginv.
  Proof.
    split.
    - apply trsSimulates_compositional.
    - apply invariant_compositional.
  Qed.

End Compositionality.

