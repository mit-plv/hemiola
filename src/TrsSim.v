Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepDet SemFacts.
Require Import Simulation Serial SerialFacts.

Require Import Omega.

Set Implicit Arguments.

Section TrsSim.
  Variables (sim: TState -> TState -> Prop)
            (ginv: TState -> Prop)
            (p: Label -> Label).

  Local Infix "≈" := sim (at level 30).

  Variables (impl spec: System).

  Definition TrsInvHolds :=
    forall ist1,
      ginv ist1 ->
      forall ihst ist2,
        trsSteps impl ist1 ihst ist2 ->
        ginv ist2.

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
    (Hsimi: sim (getStateInit impl) (getStateInit spec))
    (Hsim: TrsSimulates)
    (Hginvi: ginv (getStateInit impl))
    (Hginv: TrsInvHolds).

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
            (linv: History -> TState -> Prop)
            (p: Label -> Label).

  Local Infix "≈" := sim (at level 30).

  Variables (impl spec: System).

  Definition TrsSimSepGInvIn :=
    forall ist1,
      ginv ist1 ->
      forall imin ist2,
        step_det impl ist1 (IlblIn imin) ist2 ->
        ginv ist2.

  Definition TrsSimSepIn :=
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

  Definition TrsSimSepGInvAtomic :=
    forall min ilbl hst mouts orsout,
      Atomic impl min (ilbl :: hst) mouts orsout ->
      forall pist ist1 ist2,
        steps_det impl pist hst ist1 ->
        ginv ist1 ->
        step_det impl ist1 ilbl ist2 ->
        ginv ist2.

  Definition TrsSimSepLInvAtomic :=
    forall min ilbl hst mouts orsout,
      Atomic impl min (ilbl :: hst) mouts orsout ->
      forall pist ist1 ist2,
        steps_det impl pist hst ist1 ->
        linv hst ist1 ->
        step_det impl ist1 ilbl ist2 ->
        linv (ilbl :: hst) ist2.
  
  Definition TrsSimSepAtomic :=
    forall min ilbl hst mouts orsout,
      Atomic impl min (ilbl :: hst) mouts orsout ->
      forall pist iist,
        steps_det impl pist hst iist ->
        forall sst1,
          iist ≈ sst1 ->
          linv hst iist ->
          ginv iist ->
          forall nist,
            step_det impl iist ilbl nist ->
            match extLabel impl (getLabel ilbl) with
            | Some ielbl =>
              exists slbl sst2,
              step_det spec sst1 slbl sst2 /\
              extLabel spec (getLabel slbl) = Some (p ielbl) /\
              nist ≈ sst2
            | None => nist ≈ sst1
            end.

  Hypotheses
    (Hsimi: sim (getStateInit impl) (getStateInit spec))
    (HsimIn: TrsSimSepIn)
    (HsimAtm: TrsSimSepAtomic)
    (Hginvi: ginv (getStateInit impl))
    (HginvIn: TrsSimSepGInvIn)
    (HginvAtm: TrsSimSepGInvAtomic)
    (Hlinvi: forall st, linv nil st)
    (HlinvAtm: TrsSimSepLInvAtomic).

  Lemma trs_sim_step_steps_atomic:
    forall min ihst mouts orsout,
      Atomic impl min ihst mouts orsout ->
      forall ist1 sst1,
        ist1 ≈ sst1 ->
        ginv ist1 ->
        forall ist2,
          steps_det impl ist1 ihst ist2 ->
          exists sst2 shst,
            steps_det spec sst1 shst sst2 /\
            map p (behaviorOf impl ihst) = behaviorOf spec shst /\
            ist2 ≈ sst2 /\
            linv ihst ist2 /\ ginv ist2.
  Proof.
    induction 1; simpl; intros.

    - inv H3.
      eexists; exists nil; repeat split.
      + econstructor.
      + assumption.
      + apply Hlinvi.
      + assumption.

    - assert (Atomic impl rqin (IlblOuts (Some hdl) houts :: hst)
                     (distributeMsgs houts (deqMP from to chn mouts)) None)
        by (constructor; auto).

      pose proof H6; inv H6.
      specialize (IHAtomic _ _ H4 H5 _ H12).
      destruct IHAtomic as [ssti [shsti [? [? [? [? ?]]]]]].

      pose proof H7; eapply HsimAtm in H7.
      specialize (H7 _ _ H12 _ H10 H11 H13 _ H14).
      simpl in H7.

      destruct (extOuts impl (map tmsg_msg houts)) as [|eout eouts].
      + simpl; eexists; exists shsti; repeat split; eauto.
      + destruct H7 as [slbl [sst2 [? [? ?]]]].
        eexists; eexists (_ :: _); repeat split.
        * econstructor; eassumption.
        * simpl; rewrite H9, H16; reflexivity.
        * assumption.
        * eapply HlinvAtm; eauto.
        * eapply HginvAtm; eauto.

    - assert (Atomic impl rqin (IlblOuts (Some hdl) (rsout :: nil) :: hst) nil (Some rsout))
        by (constructor; auto).

      pose proof H4; inv H4.
      specialize (IHAtomic _ _ H2 H3 _ H10).
      destruct IHAtomic as [ssti [shsti [? [? [? [? ?]]]]]].

      pose proof H5; eapply HsimAtm in H5.
      specialize (H5 _ _ H10 _ H8 H9 H11 _ H12).
      simpl in H5.

      destruct (isExternal impl (mid_to (msg_id (id (tmsg_msg rsout))))).
      + destruct H5 as [slbl [sst2 [? [? ?]]]].
        eexists; eexists (_ :: _); repeat split.
        * econstructor; eassumption.
        * simpl; rewrite H7, H14; reflexivity.
        * assumption.
        * eapply HlinvAtm; eauto.
        * eapply HginvAtm; eauto.
      + simpl; eexists; exists shsti; repeat split; eauto.
  Qed.

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
          ist2 ≈ sst2 /\ ginv ist2.
  Proof.
    destruct 3; simpl; intros; subst.
    - inv H1; inv H5; inv H7.
      do 2 eexists; repeat split; try econstructor; assumption.
    - inv H2; inv H5.
      pose proof H7; eapply HsimIn in H7; eauto.
      eapply HginvIn in H1; eauto.
      destruct H7 as [smin [sst2 [? [? ?]]]].
      eexists; eexists (_ :: _); repeat split.
      + econstructor; [econstructor|eassumption].
      + simpl; simpl in H3; inv H3; reflexivity.
      + assumption.
      + assumption.
    - eapply trs_sim_step_steps_atomic in H1; eauto.
      dest; eauto 6.
  Qed.

  Lemma trs_sim_in_atm_simulates:
    TrsSimulates sim ginv p impl spec.
  Proof.
    unfold TrsSimulates; intros.
    destruct H1.
    eapply trs_sim_step_steps_trs in H2; eauto.
    dest; eauto.
  Qed.

End TrsSimSep.

Section TrsPreserving.

  Definition trsPreservingRule (rule: Rule) :=
    forall pre val,
      Forall (fun mout => mid_tid (msg_id mout) = mid_tid (rule_mid rule))
             (rule_outs rule pre val).

  Definition trsPreservingObj (obj: Object) :=
    Forall trsPreservingRule (obj_rules obj).

  Definition trsPreservingObs (obs: list Object) :=
    Forall trsPreservingObj obs.

  Definition trsPreservingSys (sys: System) :=
    trsPreservingObs (sys_objs sys).

End TrsPreserving.

Section TrsDisj.

  Definition TrsDisj (rules1 rules2: list Rule) :=
    forall rule1 rule2,
      In rule1 rules1 ->
      In rule2 rules2 ->
      mid_tid (rule_mid rule1) <> mid_tid (rule_mid rule2).

  Definition TrsDisjSys (sys1 sys2: System) :=
    TrsDisj (rulesOf sys1) (rulesOf sys2).

  Lemma TrsDisj_sym:
    forall ms1 ms2,
      TrsDisj ms1 ms2 ->
      TrsDisj ms2 ms1.
  Proof.
    unfold TrsDisj; intros; firstorder.
  Qed.

  Lemma TrsDisj_SubList_1:
    forall ms1 ms2,
      TrsDisj ms1 ms2 ->
      forall ms3,
        SubList ms3 ms1 ->
        TrsDisj ms3 ms2.
  Proof.
    unfold TrsDisj; intros; auto.
  Qed.

  Lemma TrsDisj_SubList_2:
    forall ms1 ms2,
      TrsDisj ms1 ms2 ->
      forall ms3,
        SubList ms3 ms2 ->
        TrsDisj ms1 ms3.
  Proof.
    unfold TrsDisj; intros; auto.
  Qed.

End TrsDisj.

Lemma trsPreservingSys_outs_same_tid:
  forall sys,
    trsPreservingSys sys ->
    forall st1 st2 hdl houts,
      step_det sys st1 (IlblOuts (Some hdl) houts) st2 ->
      Forall (fun msg => mid_tid (msg_id (tmsg_msg msg)) =
                         mid_tid (msg_id (getMsg hdl))) houts.
Proof.
  intros; inv H0.
  unfold trsPreservingSys, trsPreservingObs in H.
  eapply Forall_forall in H; eauto.
  unfold trsPreservingObj in H.
  eapply Forall_forall in H; eauto.
  unfold trsPreservingRule in H.

  clear -H H8.
  specialize (H os (msg_value (getMsg fmsg))).
  induction (rule_outs frule os (msg_value (getMsg fmsg))); [constructor|].
  simpl in *.
  inv H; constructor; auto.
  simpl; rewrite H8, H2.
  reflexivity.
Qed.  

Lemma trsPreservineSys_atomic_same_tid:
  forall sys,
    trsPreservingSys sys ->
    forall rqin mtid hst mouts orsout,
      Atomic sys rqin hst mouts orsout ->
      mtid = mid_tid (msg_id (tinfo_rqin rqin)) ->
      forall ist1 ist2,
        steps_det sys ist1 hst ist2 ->
        Forall (fun msg => mid_tid (msg_id (getMsg msg)) = mtid) mouts /\
        Forall (fun tl =>
                  match tl with
                  | IlblIn msg => mid_tid (msg_id (getMsg msg)) = mtid
                  | IlblOuts (Some hdl) _ => mid_tid (msg_id (getMsg hdl)) = mtid
                  | IlblOuts None _ => True
                  end) hst.
Proof.
  induction 2; simpl; intros; [split; repeat constructor; subst; auto| |].
  - inv H6.
    specialize (IHAtomic eq_refl _ _ H10); dest.
    split.
    + apply Forall_app.
      * apply ForallMP_deqMP; assumption.
      * eapply Forall_forall in H5; eauto.
        rewrite <-H5.
        eauto using trsPreservingSys_outs_same_tid.
    + constructor; auto.
      eapply Forall_forall in H5; eauto.
  - inv H4.
    specialize (IHAtomic eq_refl _ _ H8); dest.
    split.
    + constructor.
    + constructor; auto.
      inv H3; assumption.
Qed.

Section Compositionality.

  Variables (impl1 impl2 spec: System)
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
             (Hginv1: TrsInvHolds ginv impl1)
             (Hginv2: TrsInvHolds ginv impl2).

  Variable (impl: System).
  Hypotheses (Hmt: trsPreservingSys impl)
             (Hii: indicesOf impl = indicesOf impl1)
             (Himpl:
                forall rule iobj,
                  In rule (obj_rules iobj) ->
                  In iobj (sys_objs impl) ->
                  exists obj,
                    obj_idx obj = obj_idx iobj /\
                    In rule (obj_rules obj) /\
                    In obj (sys_objs impl1 ++ sys_objs impl2)).

  Lemma TrsDisjSys_distr_same_tid:
    forall mtid,
      (forall rule,
          mid_tid (rule_mid rule) = mtid ->
          forall iobj,
            In rule (obj_rules iobj) -> In iobj (sys_objs impl) ->
            exists obj : Object,
              obj_idx obj = obj_idx iobj /\ In rule (obj_rules obj) /\
              In obj (sys_objs impl1)) \/
      (forall rule,
          mid_tid (rule_mid rule) = mtid ->
          forall iobj,
            In rule (obj_rules iobj) -> In iobj (sys_objs impl) ->
            exists obj : Object,
              obj_idx obj = obj_idx iobj /\ In rule (obj_rules obj) /\
              In obj (sys_objs impl2)).
  Proof.
    intros.
    destruct (mtid ?<n (map (fun rule => mid_tid (rule_mid rule)) (rulesOf impl1))).
    - left; intros.
      pose proof (Himpl _ _ H0 H1).
      destruct H2 as [obj [? [? ?]]].
      apply in_app_or in H4; destruct H4.
      + exists obj; repeat split; assumption.
      + exfalso.
        pose proof (rulesOf_in _ _ H4 _ H3).
        assert (exists mrule, mid_tid (rule_mid mrule) = mtid /\ In mrule (rulesOf impl1)).
        { clear -i.
          induction (rulesOf impl1); [inv i|].
          inv i.
          { exists a; split; intuition. }
          { specialize (IHl H); dest.
            eexists; repeat split; eauto.
            right; auto.
          }
        }
        destruct H6 as [mrule [? ?]].
        specialize (Hmtdisj _ _ H7 H5).
        rewrite H, H6 in Hmtdisj; auto.
      
    - right; intros.
      pose proof (Himpl _ _ H0 H1).
      destruct H2 as [obj [? [? ?]]].
      apply in_app_or in H4; destruct H4.
      + elim n; clear n.
        pose proof (rulesOf_in _ _ H4 _ H3).
        apply in_map with (f:= fun rule => mid_tid (rule_mid rule)) in H5.
        rewrite H in H5; assumption.
      + exists obj; repeat split; assumption.
  Qed.

  Lemma atomic_steps_compositional:
    forall ist1 hst ist2,
      steps_det impl ist1 hst ist2 ->
      forall rqin mouts orsout,
        Atomic impl rqin hst mouts orsout ->
        steps_det impl1 ist1 hst ist2 \/
        steps_det impl2 ist1 hst ist2.
  Proof.
    intros.
    pose proof (TrsDisjSys_distr_same_tid (mid_tid (msg_id (tinfo_rqin rqin)))).
    pose proof (trsPreservineSys_atomic_same_tid Hmt H0 eq_refl H).
    destruct H2 as [_ ?].
    destruct H1.

    - left.
      clear -H H1 H2 Hii.
      induction H; [constructor|].
      inv H2.
      specialize (IHsteps H6); clear H6.
      econstructor; eauto; clear H IHsteps.
      inv H0.
      + constructor.
      + constructor.
        * unfold isExternal in *; rewrite <-Hii; assumption.
        * unfold isInternal in *; rewrite <-Hii; assumption.
      + simpl in H5, H7; rewrite H7 in H5.
        specialize (H1 _ H5 _ H8 H).
        destruct H1 as [obj1 [? [? ?]]].
        rewrite intOuts_same_indicesOf with (sys2:= impl1) by assumption.
        econstructor; eauto.
        unfold isInternal in *; rewrite <-Hii; assumption.

    - right.
      assert (indicesOf impl = indicesOf impl2) as Hii2 by (rewrite Hii; auto).
      clear -H H1 H2 Hii2.
      induction H; [constructor|].
      inv H2.
      specialize (IHsteps H6); clear H6.
      econstructor; eauto; clear H IHsteps.
      inv H0.
      + constructor.
      + constructor.
        * unfold isExternal in *; rewrite <-Hii2; assumption.
        * unfold isInternal in *; rewrite <-Hii2; assumption.
      + simpl in H5, H7; rewrite H7 in H5.
        specialize (H1 _ H5 _ H8 H).
        destruct H1 as [obj1 [? [? ?]]].
        rewrite intOuts_same_indicesOf with (sys2:= impl2) by assumption.
        econstructor; eauto.
        unfold isInternal in *; rewrite <-Hii2; assumption.
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
      
    - pose proof (atomic_steps_compositional H2 H); destruct H3.
      + assert (Transactional impl1 hst).
        { econstructor; eauto.
          eapply atomic_preserved; eauto.
        }
        exact (Hginv1 H1 (conj H3 H4)).
      + assert (Transactional impl2 hst).
        { econstructor; eauto.
          eapply atomic_preserved; eauto.
          rewrite Hii; assumption.
        }
        exact (Hginv2 H1 (conj H3 H4)).
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
      exists sst1, nil; repeat split.
      + constructor.
      + assumption.

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
      
    - pose proof (atomic_steps_compositional H3 H); destruct H4.
      + assert (Transactional impl1 hst).
        { econstructor; eauto.
          eapply atomic_preserved; eauto.
        }
        pose proof (Hsim1 H1 H2 (conj H4 H5)).
        rewrite behaviorOf_preserved with (impl2:= impl1) by assumption.
        assumption.
      + assert (Transactional impl2 hst).
        { econstructor; eauto.
          eapply atomic_preserved; eauto.
          rewrite Hii; assumption.
        }
        pose proof (Hsim2 H1 H2 (conj H4 H5)).
        rewrite behaviorOf_preserved with (impl2:= impl2) by (rewrite Hii; assumption).
        assumption.
  Qed.

  Theorem trsInvHolds_compositional: TrsInvHolds ginv impl.
  Proof.
    unfold TrsInvHolds in *; intros.
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
    TrsSimulates simR ginv p impl spec /\ TrsInvHolds ginv impl.
  Proof.
    split.
    - apply trsSimulates_compositional.
    - apply trsInvHolds_compositional.
  Qed.
    
End Compositionality.

