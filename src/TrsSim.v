Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepDet SemFacts.
Require Import Simulation Serial SerialFacts TrsInv.

Require Import Omega.

Set Implicit Arguments.

Section TrsSim.
  Variables (sim: TState -> TState -> Prop)
            (ginv: TState -> Prop)
            (p: Label -> Label).

  Local Infix "≈" := sim (at level 30).

  Variables (impl spec: System OrdOState).

  Definition TrsSimInit :=
    sim (getStateInit impl) (getStateInit spec).

  Definition TrsSimulates :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall ihst ist2,
        trsSteps impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps_det spec sst1 shst sst2 /\
          map p (behaviorOf impl ihst) = behaviorOf spec shst /\
          ist2 ≈ sst2.

  Hypotheses
    (Hsimi: TrsSimInit)
    (Hsim: TrsSimulates)
    (Hginvi: TrsInvInit impl ginv)
    (Hginv: TrsInv impl ginv).

  Lemma trs_simulation_steps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall trss ihst ist2,
        Forall (Transactional impl) trss ->
        ihst = concat trss ->
        steps_det impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps_det spec sst1 shst sst2 /\
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
      pose proof (Hginv H8 (conj H2 H5)).
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
          steps_det spec sst1 shst sst2 /\
          map p (behaviorOf impl ihst) = behaviorOf spec shst /\
          ist2 ≈ sst2 /\ ginv ist2.
  Proof.
    unfold seqSteps, Sequential; intros; dest; subst.
    eapply trs_simulation_steps; eauto.
  Qed.

  Theorem sequential_simulation_implies_refinement:
    seqSteps # steps_det |-- impl ⊑[p] spec.
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

  Variables (impl spec: System OrdOState).

  Definition TrsSimSilent :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall ist2,
        step_det impl ist1 emptyRLabel ist2 ->
        exists sst2,
          step_det spec sst1 emptyRLabel sst2 /\
          ist2 ≈ sst2.

  Definition TrsSimIn :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall imin ist2,
        step_det impl ist1 (IlblIn imin) ist2 ->
        exists smin sst2,
          step_det spec sst1 (IlblIn smin) sst2 /\
          extLabel spec (getLabel (IlblIn smin)) =
          Some (p (getLabel (IlblIn imin))) /\
          ist2 ≈ sst2.

  Definition TrsSimAtomic ts rq :=
    forall hst mouts,
      Atomic impl ts rq hst mouts ->
      forall ist1,
        ginv ist1 ->
        forall sst1,
          ist1 ≈ sst1 ->
          forall ist2,
            steps_det impl ist1 hst ist2 ->
            exists sst2 shst,
              steps_det spec sst1 shst sst2 /\
              map p (behaviorOf impl hst) = behaviorOf spec shst /\
              ist2 ≈ sst2.

  Hypotheses
    (Hsimi: TrsSimInit sim impl spec)
    (HsimSlt: TrsSimSilent)
    (HsimIn: TrsSimIn)
    (HsimAtm: forall ts rq, TrsSimAtomic ts rq)
    (Hinvi: TrsInvInit impl ginv)
    (HinvIn: TrsInvIn impl ginv)
    (HinvAtm: TrsInvAtomic impl ginv).

  Lemma trs_sim_step_steps_trs:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall ihst ist2,
        Transactional impl ihst ->
        steps_det impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps_det spec sst1 shst sst2 /\
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

  Definition trsPreservingRule (rule: Rule OrdOState) :=
    exists tid,
      Forall (fun mid => mid_tid mid = tid) (rule_mids rule) /\
      forall pre ins post outs,
        rule_postcond rule pre ins post outs ->
        Forall (fun mout => mid_tid (msg_id mout) = tid) outs.

  Definition trsPreservingObj (obj: Object OrdOState) :=
    Forall trsPreservingRule (obj_rules obj).

  Definition trsPreservingSys (sys: System OrdOState) :=
    Forall trsPreservingObj sys.

End TrsPreserving.

Section TrsDisj.

  Definition TrsDisj (rules1 rules2: list (Rule OrdOState)) :=
    forall rule1 rule2,
      In rule1 rules1 ->
      In rule2 rules2 ->
      forall tid1 tid2,
        In tid1 (map mid_tid (rule_mids rule1)) ->
        In tid2 (map mid_tid (rule_mids rule2)) ->
        tid1 <> tid2.

  Definition TrsDisjSys (sys1 sys2: System OrdOState) :=
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
      step_det sys st1 (IlblOuts orule hins houts) st2 ->
      exists tid,
        Forall (fun msg => mid_tid (msg_id (tmsg_msg msg)) = tid) hins /\
        Forall (fun msg => mid_tid (msg_id (tmsg_msg msg)) = tid) houts.
Proof.
  intros; inv H0; [(* anything *) exists 0; split; constructor|].
  unfold trsPreservingSys in H.
  eapply Forall_forall in H; eauto.
  unfold trsPreservingObj in H.
  eapply Forall_forall in H; eauto.
  unfold trsPreservingRule in H.
  destruct H as [tid [? ?]].
  specialize (H0 _ _ _ _ H13).
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
          steps_det sys ist1 hst ist2 ->
          Forall (fun msg => mid_tid (msg_id (getMsg msg)) = mtid) mouts /\
          Forall (fun tl =>
                    match tl with
                    | IlblIn msg => mid_tid (msg_id (getMsg msg)) = mtid
                    | IlblOuts _ ins _ =>
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
  forall tid (rules: list (Rule OrdOState)) r,
    In tid (map mid_tid (rule_mids r)) ->
    In r rules ->
    In tid (concat (map (fun rule => map mid_tid (rule_mids rule)) rules)).
Proof.
  induction rules; simpl; intros; auto.
  destruct H0; subst.
  - apply in_or_app; left; assumption.
  - apply in_or_app; right; eauto.
Qed.

Section Compositionality.

  Variables (impl1 impl2 spec: System OrdOState)
            (simR: TState -> TState -> Prop)
            (ginv: TState -> Prop)
            (p: Label -> Label).

  Local Infix "≈" := simR (at level 30).

  Hypotheses (Hidx: indicesOf impl1 = indicesOf impl2)
             (Hmt1: trsPreservingSys impl1)
             (Hmt2: trsPreservingSys impl2)
             (Hmtdisj: TrsDisjSys impl1 impl2)
             (Hsim1: TrsSimulates simR ginv p impl1 spec)
             (Hsim2: TrsSimulates simR ginv p impl2 spec)
             (Hginv1: TrsInv impl1 ginv)
             (Hginv2: TrsInv impl2 ginv).

  Variable (impl: System OrdOState).
  Hypotheses (Hmt: trsPreservingSys impl)
             (Hii: indicesOf impl = indicesOf impl1)
             (Himpl:
                forall rule iobj,
                  In rule (obj_rules iobj) ->
                  In iobj impl ->
                  exists obj,
                    obj_idx obj = obj_idx iobj /\
                    In rule (obj_rules obj) /\
                    In obj (impl1 ++ impl2)).

  Lemma TrsDisjSys_distr_same_tid:
    forall mtid,
      (forall rule,
          rule_mids rule <> nil ->
          Forall (fun mid => mid_tid mid = mtid) (rule_mids rule) ->
          forall iobj,
            In rule (obj_rules iobj) -> In iobj impl ->
            exists obj : Object OrdOState,
              obj_idx obj = obj_idx iobj /\ In rule (obj_rules obj) /\
              In obj impl1) \/
      (forall rule,
          rule_mids rule <> nil ->
          Forall (fun mid => mid_tid mid = mtid) (rule_mids rule) ->
          forall iobj,
            In rule (obj_rules iobj) -> In iobj impl ->
            exists obj : Object OrdOState,
              obj_idx obj = obj_idx iobj /\ In rule (obj_rules obj) /\
              In obj impl2).
  Proof.
    intros.
    destruct (mtid ?<n concat (map (fun rule => (map mid_tid (rule_mids rule)))
                                   (rulesOf impl1))).
    - left; intros.
      pose proof (Himpl _ _ H1 H2).
      destruct H3 as [obj [? [? ?]]].
      apply in_app_or in H5; destruct H5.
      + exists obj; repeat split; assumption.
      + exfalso.
        pose proof (rulesOf_in _ _ H5 _ H4).
        assert (exists mrule, In mtid (map mid_tid (rule_mids mrule)) /\
                              In mrule (rulesOf impl1)).
        { clear -i.
          induction (rulesOf impl1); [inv i|].
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
        destruct H7 as [mrule [? ?]].
        specialize (Hmtdisj _ _ H9 H6 H7 H8).
        elim Hmtdisj; reflexivity.
      
    - right; intros.
      pose proof (Himpl _ _ H1 H2).
      destruct H3 as [obj [? [? ?]]].
      apply in_app_or in H5; destruct H5.
      + elim n; clear n.
        pose proof (rulesOf_in _ _ H5 _ H4).
        eapply rule_mids_tid_In; eauto.
        clear -H H0; destruct (rule_mids rule); [elim H; reflexivity|].
        inv H0; left; reflexivity.
      + exists obj; repeat split; assumption.
  Qed.

  (* Lemma silent_steps_compositional: *)
  (*   forall ist1 ist2, *)
  (*     steps_det impl ist1 (emptyILabel :: nil) ist2 -> *)
  (*     steps_det impl1 ist1 (emptyILabel :: nil) ist2 \/ *)
  (*     steps_det impl2 ist1 (emptyILabel :: nil) ist2. *)
  (* Proof. *)
  (*   intros. *)
  (*   inv H; inv H3; inv H5; [left; repeat econstructor|]. *)
  (*   specialize (Himpl _ _ H8 H1). *)
  (*   destruct Himpl as [cobj [? [? ?]]]. *)
  (*   apply in_app_or in H5; destruct H5. *)
  (*   + left. *)
  (*     econstructor; [econstructor|]. *)
  (*     rewrite intOuts_same_indicesOf with (sys2:= impl1) by assumption. *)
  (*     replace emptyILabel with (IlblOuts (toTMsgs tinfo outs) (toTMsgs tinfo outs)) *)
  (*       by (rewrite H0; reflexivity). *)
  (*     eapply SdInt; eauto. *)
  (*   + right. *)
  (*     econstructor; [econstructor|]. *)
  (*     assert (indicesOf impl = indicesOf impl2) as Hii2 by (rewrite Hii; auto). *)
  (*     rewrite intOuts_same_indicesOf with (sys2:= impl2) by assumption. *)
  (*     replace emptyILabel with (IlblOuts (toTMsgs tinfo outs) (toTMsgs tinfo outs)) *)
  (*       by (rewrite H0; reflexivity). *)
  (*     eapply SdInt; eauto. *)
  (* Qed.     *)

  Lemma atomic_steps_compositional:
    forall ist1 hst ist2,
      steps_det impl ist1 hst ist2 ->
      forall ts rq mouts,
        Atomic impl ts rq hst mouts ->
        steps_det impl1 ist1 hst ist2 \/
        steps_det impl2 ist1 hst ist2.
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
        specialize (H1 _ H3 H4 _ H13 H6).
        destruct H1 as [obj1 [? [? ?]]].
        econstructor; eauto.
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
        specialize (H1 _ H2 H4 _ H16 H6).
        destruct H1 as [obj1 [? [? ?]]].
        econstructor; eauto.

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
        specialize (H1 _ H3 H4 _ H13 H6).
        destruct H1 as [obj1 [? [? ?]]].
        econstructor; eauto.
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
        specialize (H1 _ H2 H4 _ H16 H6).
        destruct H1 as [obj1 [? [? ?]]].
        econstructor; eauto.
  Qed.

  Lemma trsInvHolds_transactional_compositional:
    forall ihst,
      Transactional impl ihst ->
      forall ist1,
        ginv ist1 ->
        forall ist2,
          steps_det impl ist1 ihst ist2 ->
          ginv ist2.
  Proof.
    destruct 1; simpl; intros; subst.

    - inv H0; inv H4; inv H6; assumption.

    - assert (trsSteps impl1 ist1 (IlblIn msg :: nil) ist2).
      { split; [|econstructor; reflexivity].
        econstructor; [econstructor|].
        inv H1; inv H4; inv H6.
        eapply SdExt.
        { unfold isExternal in *.
          rewrite Hii in H1; assumption.
        }
        { unfold isInternal in *.
          rewrite Hii in H3; assumption.
        }
      }
      pose proof (Hginv1 H0 H).
      assumption.
      
    - pose proof (atomic_steps_compositional H1 H); destruct H2.
      + assert (Transactional impl1 hst).
        { econstructor; eauto.
          eapply atomic_preserved; eauto.
        }
        exact (Hginv1 H0 (conj H2 H3)).
      + assert (Transactional impl2 hst).
        { econstructor; eauto.
          eapply atomic_preserved; eauto.
          rewrite Hii; assumption.
        }
        exact (Hginv2 H0 (conj H2 H3)).
  Qed.

  Lemma trsSimulates_transactional_compositional:
    forall ihst,
      Transactional impl ihst ->
      forall ist1 sst1,
        ist1 ≈ sst1 ->
        ginv ist1 ->
        forall ist2,
          steps_det impl ist1 ihst ist2 ->
          exists (sst2 : TState) (shst : list TLabel),
            steps_det spec sst1 shst sst2 /\
            map p (behaviorOf impl ihst) = behaviorOf spec shst /\
            ist2 ≈ sst2.
  Proof.
    destruct 1; simpl; intros; subst.

    - inv H1; inv H5; inv H7.
      exists sst1, nil; repeat split; [constructor|assumption].

    - assert (trsSteps impl1 ist1 (IlblIn msg :: nil) ist2).
      { split; [|econstructor; reflexivity].
        econstructor; [econstructor|].
        inv H2; inv H5; inv H7.
        eapply SdExt.
        { unfold isExternal in *.
          rewrite Hii in H2; assumption.
        }
        { unfold isInternal in *.
          rewrite Hii in H4; assumption.
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
        rewrite behaviorOf_preserved with (impl4:= impl2) by (rewrite Hii; assumption).
        assumption.
  Qed.

  Theorem trsInvHolds_compositional: TrsInv impl ginv.
  Proof.
    unfold TrsInv in *; intros.
    destruct H0.
    eapply trsInvHolds_transactional_compositional; eauto.
  Qed.

  Theorem trsSimulates_compositional: TrsSimulates simR ginv p impl spec.
  Proof.
    unfold TrsSimulates, trsSteps in *; intros.
    destruct H1.
    eapply trsSimulates_transactional_compositional; eauto.
  Qed.

  Corollary trsSimulates_trsInvHolds_compositional:
    TrsSimulates simR ginv p impl spec /\ TrsInv impl ginv.
  Proof.
    split.
    - apply trsSimulates_compositional.
    - apply trsInvHolds_compositional.
  Qed.
    
End Compositionality.

