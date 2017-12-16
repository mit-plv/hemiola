Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepDet SemFacts.
Require Import Simulation Serial SerialFacts.

Require Import Omega.

Set Implicit Arguments.

Section TrsSim.
  Variables (sim: TState -> TState -> Prop)
            (p: Label -> Label).

  Local Infix "≈" := sim (at level 30).

  Variables (impl spec: System).

  Definition TrsSimulates :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ihst ist2,
        trsSteps impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps_det spec sst1 shst sst2 /\
          map p (behaviorOf impl ihst) = behaviorOf spec shst /\
          ist2 ≈ sst2.

  Hypothesis (Hsim: TrsSimulates).

  Lemma trs_simulation_steps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall trss ihst ist2,
        Forall (Transactional impl) trss ->
        ihst = concat trss ->
        steps_det impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps_det spec sst1 shst sst2 /\
          map p (behaviorOf impl ihst) = behaviorOf spec shst /\
          ist2 ≈ sst2.
  Proof.
    induction trss as [|trs trss]; simpl; intros; subst.
    - inv H2; exists sst1, nil; repeat split.
      + constructor.
      + assumption.
    - inv H0.
      eapply steps_split in H2; [|reflexivity].
      destruct H2 as [sti [? ?]].
      specialize (IHtrss _ _ H5 eq_refl H0).
      destruct IHtrss as [isst [ishst [? [? ?]]]].
      pose proof (Hsim H6 (conj H1 H4)).
      destruct H7 as [sst2 [shst [? [? ?]]]].
      do 2 eexists; repeat split.
      + eapply steps_append; eauto.
      + do 2 rewrite behaviorOf_app.
        rewrite map_app.
        rewrite H3, H8; reflexivity.
      + assumption.
  Qed.

  Corollary simulation_seqSteps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ihst ist2,
        seqSteps impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps_det spec sst1 shst sst2 /\
          map p (behaviorOf impl ihst) = behaviorOf spec shst /\
          ist2 ≈ sst2.
  Proof.
    unfold seqSteps, Sequential; intros; dest; subst.
    eapply trs_simulation_steps; eauto.
  Qed.

  Hypothesis (Hsimi: sim (getStateInit impl) (getStateInit spec)).

  Theorem sequential_simulation_implies_refinement:
    seqSteps # steps_det |-- impl ⊑[p] spec.
  Proof.
    unfold Simulates, Refines; intros.
    inv H.
    eapply simulation_seqSteps in H0; [|exact Hsimi].
    destruct H0 as [sst2 [shst [? [? ?]]]].
    econstructor; eauto.
  Qed.

End TrsSim.

Section TrsSimStep.
  Variables (sim: TState -> TState -> Prop)
            (p: Label -> Label).

  Local Infix "≈" := sim (at level 30).

  Variables (impl spec: System).

  Definition TrsSimStepMsgIn :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall imin ist2,
        step_det impl ist1 (IlblIn imin) ist2 ->
        exists smin sst2,
          step_det spec sst1 (IlblIn smin) sst2 /\
          extLabel spec (getLabel (IlblIn smin)) = Some (p (getLabel (IlblIn imin))) /\
          ist2 ≈ sst2.

  Definition TrsSimStepAtomic :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall tid min hst mouts,
        Atomic impl tid min hst mouts ->
        forall ists istf,
          steps_det impl ists hst istf ->
          forall ilbl ist2,
            step_det impl ist1 ilbl ist2 ->
            In ilbl hst ->
            match extLabel impl (getLabel ilbl) with
            | Some ielbl =>
              exists slbl sst2,
              step_det spec sst1 slbl sst2 /\
              extLabel spec (getLabel slbl) = Some (p ielbl) /\
              ist2 ≈ sst2
            | None =>
              (ist2 ≈ sst1 \/
               exists slbl sst2,
                 step_det spec sst1 slbl sst2 /\
                 extLabel spec (getLabel slbl) = None /\
                 ist2 ≈ sst2)
            end.

  Hypotheses (HsimIn: TrsSimStepMsgIn)
             (HsimAtm: TrsSimStepAtomic).

  Lemma trs_sim_step_steps_atomic:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall tid min ihst mouts,
        Atomic impl tid min ihst mouts ->
        forall ist2,
          steps_det impl ist1 ihst ist2 ->
          exists sst2 shst,
            steps_det spec sst1 shst sst2 /\
            map p (behaviorOf impl ihst) = behaviorOf spec shst /\
            ist2 ≈ sst2.
  Proof.
    induction 2; simpl; intros;
      [inv H2; eexists; exists nil; repeat split; [econstructor|assumption]|].

    assert (Atomic impl tid min (IlblOuts (Some hdl) houts :: hst)
                   (remove tmsg_dec hdl mouts ++ houts))
      by (constructor; auto).

    pose proof H2.
    inv H2.
    specialize (IHAtomic _ H8).
    destruct IHAtomic as [ssti [shsti [? [? ?]]]].

    eapply HsimAtm in H3; [|eapply H6].
    specialize (H3 _ _ H4 _ _ H10 (or_introl eq_refl)).
    simpl in H3.

    destruct (extOuts impl (map tmsg_msg houts)) as [|eout eouts].
    - simpl; destruct H3.
      + eexists; exists shsti; repeat split; eauto.
      + destruct H3 as [slbl [sst2 [? [? ?]]]].
        eexists; eexists (_ :: _); repeat split.
        * econstructor; eassumption.
        * simpl; rewrite H7; simpl; assumption.
        * assumption.
    - destruct H3 as [slbl [sst2 [? [? ?]]]].
      eexists; eexists (_ :: _); repeat split.
      + econstructor; eassumption.
      + simpl; rewrite H5, H7; reflexivity.
      + assumption.
  Qed.

  Lemma trs_sim_step_steps_trs:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ihst ist2,
        Transactional impl ihst ->
        steps_det impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps_det spec sst1 shst sst2 /\
          map p (behaviorOf impl ihst) = behaviorOf spec shst /\
          ist2 ≈ sst2.
  Proof.
    destruct 2; simpl; intros; subst.
    - inv H0; inv H4; inv H6.
      do 2 eexists; repeat split; try econstructor; assumption.
    - inv H1; inv H4.
      eapply HsimIn in H6; eauto.
      destruct H6 as [smin [sst2 [? [? ?]]]].
      eexists; eexists (_ :: _); repeat split.
      + econstructor; [econstructor|eassumption].
      + simpl; simpl in H1; inv H1; reflexivity.
      + assumption.
    - eapply trs_sim_step_steps_atomic; eauto.
  Qed.

  Lemma trs_sim_in_atm_simulates:
    TrsSimulates sim p impl spec.
  Proof.
    unfold TrsSimulates; intros.
    destruct H0.
    eapply trs_sim_step_steps_trs; eauto.
  Qed.

End TrsSimStep.

Section MTypePreserving.

  Definition mtPreservingPMsg (pmsg: PMsg) :=
    forall pre val,
      Forall (fun mout => mid_type (msg_id mout) = mid_type (pmsg_mid pmsg))
             (pmsg_outs pmsg pre val).

  Definition mtPreservingObj (obj: Object) :=
    Forall mtPreservingPMsg (obj_trs obj).

  Definition mtPreservingObs (obs: list Object) :=
    Forall mtPreservingObj obs.

  Definition mtPreservingSys (sys: System) :=
    mtPreservingObs (sys_objs sys).

End MTypePreserving.

Section MTypeDisj.

  Definition MTypeDisj (pmsgs1 pmsgs2: list PMsg) :=
    forall pmsg1 pmsg2,
      In pmsg1 pmsgs1 ->
      In pmsg2 pmsgs2 ->
      mid_type (pmsg_mid pmsg1) <> mid_type (pmsg_mid pmsg2).

  Definition MTypeDisjSys (sys1 sys2: System) :=
    MTypeDisj (pmsgsOf sys1) (pmsgsOf sys2).

  Lemma MTypeDisj_sym:
    forall ms1 ms2,
      MTypeDisj ms1 ms2 ->
      MTypeDisj ms2 ms1.
  Proof.
    unfold MTypeDisj; intros; firstorder.
  Qed.

  Lemma MTypeDisj_SubList_1:
    forall ms1 ms2,
      MTypeDisj ms1 ms2 ->
      forall ms3,
        SubList ms3 ms1 ->
        MTypeDisj ms3 ms2.
  Proof.
    unfold MTypeDisj; intros; auto.
  Qed.

  Lemma MTypeDisj_SubList_2:
    forall ms1 ms2,
      MTypeDisj ms1 ms2 ->
      forall ms3,
        SubList ms3 ms2 ->
        MTypeDisj ms1 ms3.
  Proof.
    unfold MTypeDisj; intros; auto.
  Qed.

End MTypeDisj.

Lemma mtPreservineSys_atomic_same_msg_type:
  forall sys,
    mtPreservingSys sys ->
    forall tid min mty hst mouts,
      Atomic sys tid min hst mouts ->
      mty = mid_type (msg_id (tmsg_msg min)) ->
      forall ist1 ist2,
        steps_det sys ist1 hst ist2 ->
        Forall (fun msg => mid_type (msg_id (tmsg_msg msg)) = mty) mouts /\
        Forall (fun tl =>
                  match tl with
                  | IlblIn msg => mid_type (msg_id (tmsg_msg msg)) = mty
                  | IlblOuts (Some hdl) _ => mid_type (msg_id (tmsg_msg hdl)) = mty
                  | IlblOuts None _ => True
                  end) hst.
Proof.
  induction 2; simpl; intros; [split; repeat constructor; auto|].

  inv H3.
  specialize (IHAtomic eq_refl _ _ H7); dest.
  split.
  - apply Forall_app.
    + apply Forall_remove; assumption.
    + eapply Forall_forall in H2; eauto.
      rewrite <-H2.

      (* NOTE: extract as a lemma? *)
      clear -H H9.
      inv H9.
      * unfold mtPreservingSys, mtPreservingObs in H.
        eapply Forall_forall in H; eauto.
        unfold mtPreservingObj in H.
        eapply Forall_forall in H; eauto.
        unfold mtPreservingPMsg in H.
        clear -H H10.
        specialize (H os (msg_value (getMsg fmsg))).
        induction (pmsg_outs fpmsg os (msg_value (getMsg fmsg))); [constructor|].
        simpl in *.
        inv H; constructor; auto.
        simpl; rewrite H10, H2.
        reflexivity.
      * unfold mtPreservingSys, mtPreservingObs in H.
        eapply Forall_forall in H; eauto.
        unfold mtPreservingObj in H.
        eapply Forall_forall in H; eauto.
        unfold mtPreservingPMsg in H.
        clear -H H10.
        specialize (H os (msg_value (getMsg hdl))).
        induction (pmsg_outs fpmsg os (msg_value (getMsg hdl))); [constructor|].
        simpl in *.
        inv H; constructor; auto.
        simpl; rewrite H10, H2.
        reflexivity.
      
  - constructor; auto.
    eapply Forall_forall in H2; eauto.
Qed.

Section Compositionality.

  Variables (impl1 impl2 spec: System)
            (simR: TState -> TState -> Prop)
            (simP: Label -> Label).

  Local Infix "≈" := simR (at level 30).

  Hypotheses (Hidx: indicesOf impl1 = indicesOf impl2)
             (Hmt1: mtPreservingSys impl1)
             (Hmt2: mtPreservingSys impl2)
             (Hmtdisj: MTypeDisjSys impl1 impl2)
             (Hsim1: TrsSimulates simR simP impl1 spec)
             (Hsim2: TrsSimulates simR simP impl2 spec).

  Variable (impl: System).
  Hypotheses (Hmt: mtPreservingSys impl)
             (Hii: indicesOf impl = indicesOf impl1)
             (Himpl:
                forall pmsg iobj,
                  In pmsg (obj_trs iobj) ->
                  In iobj (sys_objs impl) ->
                  exists obj,
                    obj_idx obj = obj_idx iobj /\
                    In pmsg (obj_trs obj) /\
                    In obj (sys_objs impl1 ++ sys_objs impl2)).

  Lemma MTypeDisjSys_distr_same_type:
    forall mty,
      (forall pmsg,
          mid_type (pmsg_mid pmsg) = mty ->
          forall iobj,
            In pmsg (obj_trs iobj) -> In iobj (sys_objs impl) ->
            exists obj : Object,
              obj_idx obj = obj_idx iobj /\ In pmsg (obj_trs obj) /\
              In obj (sys_objs impl1)) \/
      (forall pmsg,
          mid_type (pmsg_mid pmsg) = mty ->
          forall iobj,
            In pmsg (obj_trs iobj) -> In iobj (sys_objs impl) ->
            exists obj : Object,
              obj_idx obj = obj_idx iobj /\ In pmsg (obj_trs obj) /\
              In obj (sys_objs impl2)).
  Proof.
    intros.
    destruct (mty ?<n (map (fun pmsg => mid_type (pmsg_mid pmsg)) (pmsgsOf impl1))).
    - left; intros.
      pose proof (Himpl _ _ H0 H1).
      destruct H2 as [obj [? [? ?]]].
      apply in_app_or in H4; destruct H4.
      + exists obj; repeat split; assumption.
      + exfalso.
        pose proof (pmsgsOf_in _ _ H4 _ H3).
        assert (exists mpmsg, mid_type (pmsg_mid mpmsg) = mty /\ In mpmsg (pmsgsOf impl1)).
        { clear -i.
          induction (pmsgsOf impl1); [inv i|].
          inv i.
          { exists a; split; intuition. }
          { specialize (IHl H); dest.
            eexists; repeat split; eauto.
            right; auto.
          }
        }
        destruct H6 as [mpmsg [? ?]].
        specialize (Hmtdisj _ _ H7 H5).
        rewrite H, H6 in Hmtdisj; auto.
      
    - right; intros.
      pose proof (Himpl _ _ H0 H1).
      destruct H2 as [obj [? [? ?]]].
      apply in_app_or in H4; destruct H4.
      + elim n; clear n.
        pose proof (pmsgsOf_in _ _ H4 _ H3).
        apply in_map with (f:= fun pmsg => mid_type (pmsg_mid pmsg)) in H5.
        rewrite H in H5; assumption.
      + exists obj; repeat split; assumption.
  Qed.

  Lemma atomic_steps_compositional:
    forall ist1 hst ist2,
      steps_det impl ist1 hst ist2 ->
      forall tid min mouts,
        Atomic impl tid min hst mouts ->
        steps_det impl1 ist1 hst ist2 \/
        steps_det impl2 ist1 hst ist2.
  Proof.
    intros.
    pose proof (MTypeDisjSys_distr_same_type (mid_type (msg_id (tmsg_msg min)))).
    pose proof (mtPreservineSys_atomic_same_msg_type Hmt H0 eq_refl H).
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
      + simpl in H5, H9; rewrite H9 in H5.
        specialize (H1 _ H5 _ H10 H).
        destruct H1 as [obj1 [? [? ?]]].
        replace (intOuts impl (toTMsgs nts (pmsg_outs fpmsg os (msg_value (getMsg fmsg)))))
          with (intOuts impl1 (toTMsgs nts (pmsg_outs fpmsg os (msg_value (getMsg fmsg)))))
          by (unfold intOuts, isInternal; rewrite Hii; reflexivity).
        econstructor; eauto.
        unfold isExternal in *; rewrite <-Hii; assumption.
      + simpl in H5, H9; rewrite H9 in H5.
        specialize (H1 _ H5 _ H10 H).
        destruct H1 as [obj1 [? [? ?]]].
        replace (intOuts impl (toTMsgs mts (pmsg_outs fpmsg os (msg_value (getMsg fmsg)))))
          with (intOuts impl1 (toTMsgs mts (pmsg_outs fpmsg os (msg_value (getMsg fmsg)))))
          by (unfold intOuts, isInternal; rewrite Hii; reflexivity).
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
      + simpl in H5, H9; rewrite H9 in H5.
        specialize (H1 _ H5 _ H10 H).
        destruct H1 as [obj1 [? [? ?]]].
        replace (intOuts impl (toTMsgs nts (pmsg_outs fpmsg os (msg_value (getMsg fmsg)))))
          with (intOuts impl2 (toTMsgs nts (pmsg_outs fpmsg os (msg_value (getMsg fmsg)))))
          by (unfold intOuts, isInternal; rewrite Hii2; reflexivity).
        econstructor; eauto.
        unfold isExternal in *; rewrite <-Hii2; assumption.
      + simpl in H5, H9; rewrite H9 in H5.
        specialize (H1 _ H5 _ H10 H).
        destruct H1 as [obj1 [? [? ?]]].
        replace (intOuts impl (toTMsgs mts (pmsg_outs fpmsg os (msg_value (getMsg fmsg)))))
          with (intOuts impl2 (toTMsgs mts (pmsg_outs fpmsg os (msg_value (getMsg fmsg)))))
          by (unfold intOuts, isInternal; rewrite Hii2; reflexivity).
        econstructor; eauto.
        unfold isInternal in *; rewrite <-Hii2; assumption.
  Qed.
  
  Lemma transactional_steps_compositional:
    forall ihst,
      Transactional impl ihst ->
      forall ist1 sst1,
        ist1 ≈ sst1 ->
        forall ist2,
          steps_det impl ist1 ihst ist2 ->
          exists (sst2 : TState) (shst : list TLabel),
            steps_det spec sst1 shst sst2 /\
            map simP (behaviorOf impl ihst) = behaviorOf spec shst /\
            ist2 ≈ sst2.
  Proof.
    induction 1; simpl; intros; subst.

    - inv H0; inv H4; inv H6.
      exists sst1, nil; repeat split.
      + constructor.
      + assumption.

    - assert (trsSteps impl1 ist1 (IlblIn (toTMsgU msg) :: nil) ist2).
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
      pose proof (Hsim1 H0 H).
      simpl; simpl in H2; assumption.
      
    - pose proof (atomic_steps_compositional H1 H); destruct H2.
      + assert (Transactional impl1 hst).
        { econstructor.
          eapply atomic_preserved; eauto.
        }
        pose proof (Hsim1 H0 (conj H2 H3)).
        rewrite behaviorOf_preserved with (impl2:= impl1) by assumption.
        assumption.
      + assert (Transactional impl2 hst).
        { econstructor.
          eapply atomic_preserved; eauto.
          rewrite Hii; assumption.
        }
        pose proof (Hsim2 H0 (conj H2 H3)).
        rewrite behaviorOf_preserved with (impl2:= impl2) by (rewrite Hii; assumption).
        assumption.
  Qed.

  Theorem trsSimulates_compositional: TrsSimulates simR simP impl spec.
  Proof.
    unfold TrsSimulates, trsSteps in *; intros.
    destruct H0.
    eapply transactional_steps_compositional; eauto.
  Qed.

End Compositionality.

