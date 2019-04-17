Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvMsg RqRsInvLock.
Require Import RqUpRed.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section RqUpStart.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).
  
  Definition NonRqUpL (lbl: MLabel) :=
    match lbl with
    | RlblEmpty _ => True
    | RlblIns _ => True
    | RlblOuts _ => True
    | RlblInt _ _ _ routs => forall oidxTo, ~ RqUpMsgs dtr oidxTo routs
    end.

  Ltac disc_NonRqUpL :=
    repeat
      match goal with
      | [ |- NonRqUpL _] => red
      | [ |- forall _, ~ RqUpMsgs _ _ _] =>
        let oidxTo := fresh "oidxTo" in
        let Hx := fresh "H" in
        intros oidxTo Hx
      | [H: RqUpMsgs _ _ _ |- _] =>
        let cidx := fresh "cidx" in
        let rqUp := fresh "rqUp" in
        destruct H as [cidx [rqUp ?]]; dest
      | [H: _ :: _ = _ :: _ |- _] => inv H; simpl in *
      | [H1: ?t = MRq, H2: ?t = MRs |- _] => rewrite H1 in H2; discriminate
      end.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok.

  Lemma rqUp_start_ok_base:
    forall st1 st2 oidx ridx rins routs,
      Reachable (steps step_m) sys st1 ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      (exists roidx, RqUpMsgs dtr roidx routs) \/
      NonRqUpL (RlblInt oidx ridx rins routs).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H2).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      right; disc_NonRqUpL.
    - disc_rule_conds.
      right; disc_NonRqUpL.

    - disc_rule_conds.
      + left.
        pose proof (rqEdgeUpFrom_Some H _ H6).
        destruct H14 as [rsUp [down [pidx ?]]]; dest.
        eexists; red.
        do 2 eexists; eauto.
      + right; disc_NonRqUpL; subst.
        eapply RqRsDownMatch_rq_rs in H20; [|left; reflexivity].
        destruct H20 as [rcidx [rsUp ?]]; dest.
        solve_midx_false.
      + right; disc_NonRqUpL; subst.
        eapply RqRsDownMatch_rq_rs in H6; [|left; reflexivity].
        destruct H6 as [rcidx [rsUp ?]]; dest.
        solve_midx_false.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + right; disc_NonRqUpL.
      + right; disc_NonRqUpL.
      + right; disc_NonRqUpL.

    - disc_rule_conds.
      right; disc_NonRqUpL; subst.
      eapply RqRsDownMatch_rq_rs in H20; [|left; reflexivity].
      destruct H20 as [rcidx [rsUp ?]]; dest.
      solve_midx_false.
  Qed.

  Lemma rqUp_start_ok_end:
    forall rqUp cidx roidx inits ruins pruhst ruouts,
      msg_type (valOf rqUp) = MRq ->
      parentIdxOf dtr cidx = Some roidx ->
      rqEdgeUpFrom dtr cidx = Some (idOf rqUp) ->
      Atomic msg_dec inits ruins pruhst ruouts [rqUp] ->
      forall oidx ridx routs st1 st2,
        Reachable (steps step_m) sys st1 ->
        step_m sys st1 (RlblInt oidx ridx [rqUp] routs) st2 ->
        exists ruhst nhst,
          RlblInt oidx ridx [rqUp] routs :: pruhst = nhst ++ ruhst /\
          (ruhst = nil \/
           (exists roidx0 rqUps ruins0 ruouts0,
               RqUpMsgs dtr roidx0 rqUps /\
               Atomic msg_dec inits ruins0 ruhst ruouts0 rqUps /\
               SubList rqUps (ruouts ++ routs) /\
               (nhst = nil \/
                (exists nins nouts,
                    Atomic msg_dec rqUps nins nhst nouts routs /\
                    In roidx0 (oindsOf nhst))))) /\
          Forall NonRqUpL nhst.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H6).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      eexists pruhst, [_].
      repeat ssplit.
      + reflexivity.
      + right; do 4 eexists.
        repeat ssplit; try eassumption.
        * red; do 2 eexists.
          repeat ssplit; eauto.
        * apply SubList_app_1.
          eapply atomic_eouts_in; eauto.
        * right; do 2 eexists; split.
          { econstructor. }
          { left; reflexivity. }
      + constructor; [|constructor].
        disc_NonRqUpL; subst.

    - exfalso; disc_rule_conds.
      solve_midx_false.

    - disc_rule_conds.
      + eexists (_ :: pruhst), nil.
        repeat ssplit.
        * reflexivity.
        * right.
          pose proof (rqEdgeUpFrom_Some H _ H11).
          destruct H7 as [rsUp [down [pidx ?]]]; dest.
          exists pidx, [(rqTo, rqtm)]; do 2 eexists.
          repeat ssplit.
          { red; do 2 eexists.
            repeat ssplit; eauto.
          }
          { econstructor; try reflexivity; try eassumption.
            { discriminate. }
            { apply SubList_refl. }
            { rewrite removeL_nil; reflexivity. }
          }
          { apply SubList_app_2, SubList_refl. }
          { left; reflexivity. }
        * constructor.
      + eexists pruhst, [_].
        repeat ssplit.
        * reflexivity.
        * right; do 4 eexists.
          repeat ssplit; try eassumption.
          { red; do 2 eexists.
            repeat ssplit; eauto.
          }
          { apply SubList_app_1.
            eapply atomic_eouts_in; eauto.
          }
          { right; do 2 eexists; split.
            { econstructor. }
            { left; reflexivity. }
          }
        * constructor; [|constructor].
          disc_NonRqUpL; subst.
          eapply RqRsDownMatch_rq_rs in H27; [|left; reflexivity].
          destruct H27 as [rcidx [rsUp ?]]; dest.
          solve_midx_false.
      + exfalso; solve_midx_false.

    - exfalso; disc_rule_conds.
    - exfalso; disc_rule_conds.
  Qed.

  Lemma nonRqUpL_label_outs_no_rqUp:
    forall oidx ridx rins routs st1 st2,
      Reachable (steps step_m) sys st1 ->
      NonRqUpL (RlblInt oidx ridx rins routs) ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      Forall (fun out => forall oidxTo, ~ RqUpMsgs dtr oidxTo [out]) routs.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H2) as Hfinv.
    inv_step.
    
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      repeat constructor.
      disc_NonRqUpL.
    - disc_rule_conds.
      repeat constructor.
      disc_NonRqUpL.
    - disc_rule_conds.
      + pose proof (rqEdgeUpFrom_Some H _ H6).
        destruct H14 as [rsUp [down [pidx ?]]]; dest.
        elim (H3 pidx).
        do 2 eexists; eauto.
      + apply Forall_forall; intros [midx msg] ?.
        apply in_map with (f:= idOf) in H5; simpl in H5.
        disc_NonRqUpL.
        eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
        destruct H20 as [rcidx [rsUp ?]]; dest.
        solve_midx_false.
      + apply Forall_forall; intros [midx msg] ?.
        apply in_map with (f:= idOf) in H7; simpl in H7.
        disc_NonRqUpL.
        eapply RqRsDownMatch_rq_rs in H6; [|eassumption].
        destruct H6 as [rcidx [rsUp ?]]; dest.
        solve_midx_false.
    - good_footprint_get (obj_idx obj).
      disc_rule_conds;
        try (repeat constructor; disc_NonRqUpL; fail).
    - disc_rule_conds.
      apply Forall_forall; intros [midx msg] ?.
      apply in_map with (f:= idOf) in H5; simpl in H5.
      disc_NonRqUpL.
      eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
      destruct H20 as [rcidx [rsUp ?]]; dest.
      solve_midx_false.
  Qed.

  Lemma nonRqUpL_atomic_msg_outs_no_rqUp:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      Forall NonRqUpL hst ->
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall st2,
          steps step_m sys st1 hst st2 ->
          Forall (fun eout => forall oidxTo, ~ RqUpMsgs dtr oidxTo [eout]) eouts.
  Proof.
    induction 1; simpl; intros; subst.
    - inv_steps.
      inv H.
      eapply nonRqUpL_label_outs_no_rqUp; eauto.
    - inv_steps.
      inv H5.
      apply Forall_app.
      + apply forall_removeL; eauto.
      + eapply nonRqUpL_label_outs_no_rqUp;
          try eapply H10; eauto.
  Qed.

  Lemma nonRqUp_ins_nonRqUpL:
    forall st1 st2 oidx ridx rins routs,
      Reachable (steps step_m) sys st1 ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      Forall (fun rin => forall oidxTo, ~ RqUpMsgs dtr oidxTo [rin]) rins ->
      NonRqUpL (RlblInt oidx ridx rins routs).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H2).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds; disc_NonRqUpL.
    - disc_rule_conds; disc_NonRqUpL.
    - disc_rule_conds.
      + elim (H24 (obj_idx obj)).
        do 2 eexists; eauto.
      + disc_NonRqUpL; subst.
        eapply RqRsDownMatch_rq_rs in H21; [|left; reflexivity].
        destruct H21 as [rcidx [rsUp ?]]; dest.
        solve_midx_false.
      + disc_NonRqUpL; subst.
        eapply RqRsDownMatch_rq_rs in H7; [|left; reflexivity].
        destruct H7 as [rcidx [rsUp ?]]; dest.
        solve_midx_false.
    - disc_rule_conds; disc_NonRqUpL.
    - disc_rule_conds.
      disc_NonRqUpL; subst.
      eapply RqRsDownMatch_rq_rs in H21; [|left; reflexivity].
      destruct H21 as [rcidx [rsUp ?]]; dest.
      solve_midx_false.
  Qed.

  Lemma rqUp_start_ok:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall st1 st2,
        Reachable (steps step_m) sys st1 ->
        steps step_m sys st1 hst st2 ->
        exists ruhst nhst,
          hst = nhst ++ ruhst /\
          (ruhst = nil \/
           exists roidx rqUps ruins ruouts,
             RqUpMsgs dtr roidx rqUps /\
             Atomic msg_dec inits ruins ruhst ruouts rqUps /\
             SubList rqUps outs /\
             (nhst = nil \/
              exists nins nouts,
                Atomic msg_dec rqUps nins nhst nouts eouts /\
                In roidx (oindsOf nhst))) /\
          Forall NonRqUpL nhst.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst.

    - inv_steps.
      eapply rqUp_start_ok_base in H9; [|eassumption].
      destruct H9.
      + destruct H3 as [roidx ?].
        eexists; exists nil.
        repeat ssplit.
        * reflexivity.
        * right; do 4 eexists.
          repeat ssplit; eauto.
          { econstructor. }
          { apply SubList_refl. }
        * constructor.
      + exists nil; eexists.
        repeat ssplit.
        * rewrite app_nil_r; reflexivity.
        * left; reflexivity.
        * constructor; auto.

    - inv_steps.
      specialize (IHAtomic _ _ H8 H10).
      destruct IHAtomic as [pruhst [pnhst ?]]; dest; subst.
      destruct H6; subst.

      + exists nil.
        exists (RlblInt oidx ridx rins routs :: pnhst).
        repeat rewrite app_nil_r in *.
        repeat ssplit.
        * reflexivity.
        * left; reflexivity.
        * constructor; [|assumption].
          eapply nonRqUpL_atomic_msg_outs_no_rqUp in H2; try eassumption.
          eapply SubList_forall in H4; [|eassumption].
          assert (Reachable (steps step_m) sys st3) by eauto; clear H8.
          eapply nonRqUp_ins_nonRqUpL; eauto.

      + destruct H5 as [roidx [rqUps [ruins [ruouts ?]]]]; dest.
        destruct H11; subst.

        * simpl in *.
          pose proof (atomic_unique H2 H6); dest; subst; clear H11.
          red in H5; destruct H5 as [cidx [rqUp ?]]; dest; subst.
          assert (rins = [rqUp]); subst.
          { inv_step; inv H24.
            destruct rins; [elim H3; reflexivity|].
            pose proof (H4 i (or_introl eq_refl)); dest_in.
            destruct rins; [reflexivity|].
            specialize (H4 i0 (or_intror (or_introl eq_refl))); dest_in.
            red in H12; simpl in H12.
            inv H12; elim H16; left; reflexivity.
          }
          pose proof (reachable_steps H8 H10).
          rewrite removeL_nil; simpl.
          eapply rqUp_start_ok_end; eauto.

        * destruct H11 as [pnins [pnouts [? ?]]].
          exists pruhst, (RlblInt oidx ridx rins routs :: pnhst).
          repeat ssplit.
          { reflexivity. }
          { right; exists roidx, rqUps, ruins, ruouts.
            repeat ssplit; try assumption.
            { apply SubList_app_1; assumption. }
            { right; do 2 eexists; split.
              { econstructor; eauto. }
              { right; assumption. }
            }
          }
          { constructor; [|assumption].
            assert (Reachable (steps step_m) sys st3) by eauto.
            eapply steps_split in H10; [|reflexivity].
            destruct H10 as [sti [? ?]].
            eapply nonRqUpL_atomic_msg_outs_no_rqUp in H11;
              [|assumption
               |eapply reachable_steps; [|eapply H10]; assumption
               |eassumption].
            eapply SubList_forall in H4; [|eassumption].
            eapply nonRqUp_ins_nonRqUpL; try eapply H12; eauto.
          }
  Qed.

End RqUpStart.

Lemma parent_parent_in_False:
  forall dtr (Hwf: WfDTree dtr) oidx1 oidx2 oidx3,
    parentIdxOf dtr oidx1 = Some oidx2 ->
    parentIdxOf dtr oidx2 = Some oidx3 ->
    In oidx3 (subtreeIndsOf dtr oidx1) ->
    False.
Proof.
  intros.
  pose proof (subtreeIndsOf_child_in Hwf _ H).
  pose proof (subtreeIndsOf_child_SubList Hwf _ H0).
  apply H3 in H2.
  pose proof (subtreeIndsOf_In_each_other_eq Hwf _ _ H1 H2); subst.
  eapply parentIdxOf_asym; eassumption.
Qed.

Section Separation.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypothesis (Hrrs: RqRsSys dtr sys).

  Definition RqRsMsgFrom (oidx: IdxT) (idm: Id Msg) :=
    rqEdgeUpFrom dtr oidx = Some (idOf idm) \/
    rsEdgeUpFrom dtr oidx = Some (idOf idm) \/
    (exists cidx,
        parentIdxOf dtr cidx = Some oidx /\
        edgeDownTo dtr cidx = Some (idOf idm)).

  Definition RqRsMsgTo (oidx: IdxT) (idm: Id Msg) :=
    (exists cidx,
        parentIdxOf dtr cidx = Some oidx /\
        rqEdgeUpFrom dtr cidx = Some (idOf idm)) \/
    (exists cidx,
        parentIdxOf dtr cidx = Some oidx /\
        rsEdgeUpFrom dtr cidx = Some (idOf idm)) \/
    edgeDownTo dtr oidx = Some (idOf idm).

  Lemma RqRsMsgFrom_rqEdgeUpFrom_eq:
    forall oidx1 oidx2 midx msg,
      RqRsMsgFrom oidx1 (midx, msg) ->
      rqEdgeUpFrom dtr oidx2 = Some midx ->
      oidx1 = oidx2.
  Proof.
    destruct Hrrs as [? [? ?]].
    intros; destruct H2 as [|[|]]; simpl in *.
    - repeat disc_rule_minds; auto.
    - solve_midx_false.
    - destruct H2 as [cidx [? ?]].
      solve_midx_false.
  Qed.

  Lemma RqRsMsgFrom_rsEdgeUpFrom_eq:
    forall oidx1 oidx2 midx msg,
      RqRsMsgFrom oidx1 (midx, msg) ->
      rsEdgeUpFrom dtr oidx2 = Some midx ->
      oidx1 = oidx2.
  Proof.
    destruct Hrrs as [? [? ?]].
    intros; destruct H2 as [|[|]]; simpl in *.
    - solve_midx_false.
    - repeat disc_rule_minds; auto.
    - destruct H2 as [cidx [? ?]].
      solve_midx_false.
  Qed.

  Lemma RqRsMsgFrom_edgeDownTo_eq:
    forall oidx1 cidx oidx2 midx msg,
      RqRsMsgFrom oidx1 (midx, msg) ->
      edgeDownTo dtr cidx = Some midx ->
      parentIdxOf dtr cidx = Some oidx2 ->
      oidx1 = oidx2.
  Proof.
    destruct Hrrs as [? [? ?]].
    intros; destruct H2 as [|[|]]; simpl in *.
    - solve_midx_false.
    - solve_midx_false.
    - destruct H2 as [rcidx [? ?]].
      repeat disc_rule_minds; auto.
  Qed.

  Lemma RqRsMsgTo_rqEdgeUpFrom_eq:
    forall oidx1 cidx oidx2 midx msg,
      RqRsMsgTo oidx1 (midx, msg) ->
      parentIdxOf dtr cidx = Some oidx2 ->
      rqEdgeUpFrom dtr cidx = Some midx ->
      oidx1 = oidx2.
  Proof.
    destruct Hrrs as [? [? ?]].
    intros; destruct H2 as [|[|]]; simpl in *.
    - destruct H2 as [rcidx [? ?]].
      repeat disc_rule_minds; auto.
    - destruct H2 as [rcidx [? ?]].
      solve_midx_false.
    - solve_midx_false.
  Qed.

  Lemma RqRsMsgTo_rsEdgeUpFrom_eq:
    forall oidx1 cidx oidx2 midx msg,
      RqRsMsgTo oidx1 (midx, msg) ->
      parentIdxOf dtr cidx = Some oidx2 ->
      rsEdgeUpFrom dtr cidx = Some midx ->
      oidx1 = oidx2.
  Proof.
    destruct Hrrs as [? [? ?]].
    intros; destruct H2 as [|[|]]; simpl in *.
    - destruct H2 as [rcidx [? ?]].
      solve_midx_false.
    - destruct H2 as [rcidx [? ?]].
      repeat disc_rule_minds; auto.
    - solve_midx_false.
  Qed.

  Lemma RqRsMsgTo_edgeDownTo_eq:
    forall oidx1 oidx2 midx msg,
      RqRsMsgTo oidx1 (midx, msg) ->
      edgeDownTo dtr oidx2 = Some midx ->
      oidx1 = oidx2.
  Proof.
    destruct Hrrs as [? [? ?]].
    intros; destruct H2 as [|[|]]; simpl in *.
    - destruct H2 as [rcidx [? ?]].
      solve_midx_false.
    - destruct H2 as [rcidx [? ?]].
      solve_midx_false.
    - repeat disc_rule_minds; auto.
  Qed.
  
  Ltac disc_RqRsMsgFrom :=
    match goal with
    | [H: exists _, RqRsMsgFrom _ _ /\ _ |- _] =>
      let oidx := fresh "oidx" in
      destruct H as [oidx [? ?]]
    | [H1: rqEdgeUpFrom _ ?oidx1 = Some ?rqUp,
       H2: RqRsMsgFrom ?oidx2 (?rqUp, _) |- _] =>
      eapply RqRsMsgFrom_rqEdgeUpFrom_eq in H2; [|eapply H1]; subst
    | [H1: rsEdgeUpFrom _ ?oidx1 = Some ?rsUp,
       H2: RqRsMsgFrom ?oidx2 (?rsUp, _) |- _] =>
      eapply RqRsMsgFrom_rsEdgeUpFrom_eq in H2; [|eapply H1]; subst
    | [H1: edgeDownTo _ ?cidx = Some ?down,
       H2: parentIdxOf _ ?cidx = Some ?oidx1,
       H3: RqRsMsgFrom ?oidx2 (?down, _) |- _] =>
      eapply RqRsMsgFrom_edgeDownTo_eq in H3; [|eapply H1|eapply H2]; subst
    end.

  Ltac disc_RqRsMsgTo :=
    match goal with
    | [H: exists _, RqRsMsgTo _ _ /\ _ |- _] =>
      let oidx := fresh "oidx" in
      destruct H as [oidx [? ?]]
    | [H1: parentIdxOf _ ?cidx = Some ?oidx1,
       H2: rqEdgeUpFrom _ ?cidx = Some ?rqUp,
       H3: RqRsMsgTo ?oidx2 (?rqUp, _) |- _] =>
      eapply RqRsMsgTo_rqEdgeUpFrom_eq in H3; [|eapply H1|eapply H2]; subst
    | [H1: parentIdxOf _ ?cidx = Some ?oidx1,
       H2: rsEdgeUpFrom _ ?oidx1 = Some ?rsUp,
       H3: RqRsMsgTo ?oidx2 (?rsUp, _) |- _] =>
      eapply RqRsMsgTo_rsEdgeUpFrom_eq in H3; [|eapply H1|eapply H2]; subst
    | [H1: edgeDownTo _ ?cidx = Some ?down,
       H2: RqRsMsgTo ?oidx2 (?down, _) |- _] =>
      eapply RqRsMsgTo_edgeDownTo_eq in H2; [|eapply H1]; subst
    end.
  
  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_RqRsMsgTo.

  Lemma step_msg_ins:
    forall st1 st2 oidx ridx rins routs,
      Reachable (steps step_m) sys st1 ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      Forall (RqRsMsgTo oidx) rins.
  Proof.
    destruct Hrrs as [? [? ?]].
    intros.
    pose proof (footprints_ok H0 H2).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.
    - disc_rule_conds.
      constructor; [|constructor].
      left; eauto.
    - disc_rule_conds.
      constructor; [|constructor].
      right; right; eauto.
    - disc_rule_conds.
      + constructor; [|constructor].
        left; eauto.
      + constructor; [|constructor].
        left; eauto.
      + constructor; [|constructor].
        right; right; eauto.
    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + constructor; [|constructor].
        right; right; eauto.
      + rewrite <-H29 in H22.
        apply Forall_forall; intros [midx msg] ?.
        apply in_map with (f:= idOf) in H6.
        eapply RqRsDownMatch_rs_rq in H22; [|eassumption].
        destruct H22 as [cidx [down ?]]; dest.
        right; left; eauto.
      + rewrite <-H29 in H7.
        apply Forall_forall; intros [midx msg] ?.
        apply in_map with (f:= idOf) in H11.
        eapply RqRsDownMatch_rs_rq in H7; [|eassumption].
        destruct H7 as [cidx [down ?]]; dest.
        right; left; eauto.
    - disc_rule_conds.
      constructor; [|constructor].
      right; right; eauto.
  Qed.

  Lemma atomic_inits_bounded:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cover,
          SubList (oindsOf hst) cover ->
          Forall (fun init =>
                    exists oidx,
                      RqRsMsgTo oidx init /\ In oidx cover) inits.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst.
    - inv_steps.
      apply step_msg_ins in H10; [|assumption].
      eapply Forall_impl; [|eassumption].
      intros idm ?.
      exists oidx; split; auto.
      apply SubList_singleton_In; assumption.
    - inv_steps.
      apply SubList_cons_inv in H10; dest.
      eauto.
  Qed.

  Corollary atomic_inits_in_history:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        Forall (fun init =>
                  exists oidx,
                    RqRsMsgTo oidx init /\ In oidx (oindsOf hst)) inits.
  Proof.
    intros.
    eapply atomic_inits_bounded in H; try eassumption.
    apply SubList_refl.
  Qed.
  
  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_RqRsMsgFrom.
    
  Lemma step_msg_outs:
    forall st1 st2 oidx ridx rins routs,
      Reachable (steps step_m) sys st1 ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      Forall (RqRsMsgFrom oidx) routs.
  Proof.
    destruct Hrrs as [? [? ?]].
    intros.
    pose proof (footprints_ok H0 H2).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.
    - disc_rule_conds.
      constructor; [|constructor].
      right; right; eauto.
    - disc_rule_conds.
      constructor; [|constructor].
      right; left; eauto.
    - disc_rule_conds.
      + constructor; [|constructor].
        left; eauto.
      + apply Forall_forall; intros [midx msg] ?.
        apply in_map with (f:= idOf) in H5.
        eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
        destruct H20 as [cidx [rsUp ?]]; dest.
        right; right; eauto.
      + apply Forall_forall; intros [midx msg] ?.
        apply in_map with (f:= idOf) in H7.
        eapply RqRsDownMatch_rq_rs in H6; [|eassumption].
        destruct H6 as [cidx [rsUp ?]]; dest.
        right; right; eauto.
    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + constructor; [|constructor].
        right; right; eauto.
      + constructor; [|constructor].
        right; right; eauto.
      + constructor; [|constructor].
        right; left; eauto.
    - disc_rule_conds.
      apply Forall_forall; intros [midx msg] ?.
      apply in_map with (f:= idOf) in H5.
      eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
      destruct H20 as [cidx [rsUp ?]]; dest.
      right; right; eauto.
  Qed.

  Lemma atomic_ext_outs_bounded:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cover,
          SubList (oindsOf hst) cover ->
          Forall (fun eout =>
                    exists oidx,
                      RqRsMsgFrom oidx eout /\ In oidx cover) eouts.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst.
    - inv_steps.
      apply step_msg_outs in H10; [|assumption].
      eapply Forall_impl; [|eassumption].
      intros idm ?.
      exists oidx; split; auto.
      apply SubList_singleton_In; assumption.
    - inv_steps.
      apply SubList_cons_inv in H10; dest.
      specialize (IHAtomic _ _ H8 H11 _ H6).
      apply Forall_app.
      + apply forall_removeL; assumption.
      + apply step_msg_outs in H13; [|eauto].
        eapply Forall_impl; [|eassumption].
        intros idm ?.
        exists oidx; split; auto.
  Qed.

  Corollary atomic_ext_outs_in_history:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        Forall (fun eout =>
                  exists oidx,
                    RqRsMsgFrom oidx eout /\ In oidx (oindsOf hst)) eouts.
  Proof.
    intros.
    eapply atomic_ext_outs_bounded in H; try eassumption.
    apply SubList_refl.
  Qed.

  Corollary atomic_rqUp_out_in_history:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall oidx rqUp,
          rqEdgeUpFrom dtr oidx = Some rqUp ->
          In rqUp (idsOf eouts) ->
          In oidx (oindsOf hst).
  Proof.
    intros.
    eapply atomic_ext_outs_in_history in H; try eassumption.
    apply in_map_iff in H3; destruct H3 as [[rrqUp rqm] [? ?]].
    simpl in *; subst.
    rewrite Forall_forall in H.
    specialize (H _ H4); destruct H as [roidx [? ?]].
    disc_RqRsMsgFrom; assumption.
  Qed.

  Corollary atomic_rsUp_out_in_history:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall oidx rsUp,
          rsEdgeUpFrom dtr oidx = Some rsUp ->
          In rsUp (idsOf eouts) ->
          In oidx (oindsOf hst).
  Proof.
    intros.
    eapply atomic_ext_outs_in_history in H; try eassumption.
    apply in_map_iff in H3; destruct H3 as [[rrsUp rsm] [? ?]].
    simpl in *; subst.
    rewrite Forall_forall in H.
    specialize (H _ H4); destruct H as [roidx [? ?]].
    disc_RqRsMsgFrom; assumption.
  Qed.

  Corollary atomic_down_out_in_history:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall pidx oidx down,
          edgeDownTo dtr oidx = Some down ->
          parentIdxOf dtr oidx = Some pidx ->
          In down (idsOf eouts) ->
          In pidx (oindsOf hst).
  Proof.
    intros.
    eapply atomic_ext_outs_in_history in H; try eassumption.
    apply in_map_iff in H4; destruct H4 as [[rdown dm] [? ?]].
    simpl in *; subst.
    rewrite Forall_forall in H.
    specialize (H _ H5); destruct H as [roidx [? ?]].
    disc_RqRsMsgFrom; assumption.
  Qed.
  
  Lemma atomic_msg_outs_disj:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cover,
          DisjList (oindsOf hst) cover ->
          Forall (fun eout =>
                    exists oidx,
                      RqRsMsgFrom oidx eout /\ ~ In oidx cover) eouts.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst.
    - inv_steps.
      apply step_msg_outs in H10; [|assumption].
      eapply Forall_impl; [|eassumption].
      intros idm ?.
      exists oidx; split; auto.
      specialize (H4 oidx); destruct H4; auto.
      elim H4; left; reflexivity.
    - inv_steps.
      apply DisjList_cons in H10; dest.
      specialize (IHAtomic _ _ H8 H11 _ H6).
      apply Forall_app.
      + apply forall_removeL; assumption.
      + apply step_msg_outs in H13; [|eauto].
        eapply Forall_impl; [|eassumption].
        intros idm ?.
        exists oidx; split; auto.
  Qed.

  (*! Separation by an unvisited object *)
  
  Lemma step_separation_inside_child_ok:
    forall cidx oidx pidx,
      parentIdxOf dtr cidx = Some pidx ->
      oidx <> pidx ->
      forall st1 st2 ridx rins routs,
        Reachable (steps step_m) sys st1 ->
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        Forall
          (fun eout =>
             exists oidx,
               RqRsMsgFrom oidx eout /\
               In oidx (subtreeIndsOf dtr cidx)) rins ->
        In oidx (subtreeIndsOf dtr cidx).
  Proof.
    destruct Hrrs as [? [? ?]].
    intros.
    pose proof (footprints_ok H0 H4).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.
    - disc_rule_conds.
      destruct H.
      eapply inside_parent_in; try eapply H; try eassumption.
      intro Hx; subst.
      disc_rule_conds; auto.
    - disc_rule_conds.
      pose proof (edgeDownTo_Some H _ H26).
      destruct H.
      destruct H8 as [rqUp [rsUp [rpidx ?]]]; dest.
      disc_RqRsMsgFrom.
      eapply inside_child_in in H21; try eassumption.

    - disc_rule_conds.
      + destruct H.
        eapply inside_parent_in; try eapply H; try eassumption.
        intro Hx; subst.
        disc_rule_conds; auto.
      + destruct H.
        eapply inside_parent_in; try eapply H; try eassumption.
        intro Hx; subst.
        disc_rule_conds; auto.
      + pose proof (edgeDownTo_Some H _ H5).
        destruct H.
        destruct H14 as [rqUp [rsUp [rpidx ?]]]; dest.
        disc_RqRsMsgFrom.
        eapply inside_child_in in H10; try eassumption.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + pose proof (edgeDownTo_Some H _ H11).
        destruct H28 as [rqUp [rsUp [rpidx ?]]]; dest.
        destruct H.
        disc_RqRsMsgFrom.
        eapply inside_child_in in H27; try eassumption.
      + assert (exists rcidx rsUp rsm,
                   In (rsUp, rsm) rins /\
                   parentIdxOf dtr rcidx = Some (obj_idx obj) /\
                   rsEdgeUpFrom dtr rcidx = Some rsUp /\
                   In rcidx (subtreeIndsOf dtr cidx)).
        { rewrite <-H32 in H25.
          pose proof (RqRsDownMatch_rs_not_nil H25).
          destruct rins as [|[rmidx rmsg] rins]; [exfalso; auto|].
          eapply RqRsDownMatch_rs_rq in H25; [|left; reflexivity].
          destruct H25 as [rcidx [down ?]]; dest.
          simpl in *.
          inv H6; repeat disc_RqRsMsgFrom.
          do 3 eexists.
          repeat ssplit; [left; reflexivity| | |]; try eassumption.
        }
        destruct H9 as [rcidx [rsUp [rsum ?]]]; dest.
        destruct H.
        eapply inside_parent_in; try eapply H; try eassumption.
        intro Hx; subst.
        disc_rule_conds; auto.
      + assert (exists rcidx rsUp rsm,
                   In (rsUp, rsm) rins /\
                   parentIdxOf dtr rcidx = Some (obj_idx obj) /\
                   rsEdgeUpFrom dtr rcidx = Some rsUp /\
                   In rcidx (subtreeIndsOf dtr cidx)).
        { rewrite <-H32 in H10.
          pose proof (RqRsDownMatch_rs_not_nil H10).
          destruct rins as [|[rmidx rmsg] rins]; [exfalso; auto|].
          eapply RqRsDownMatch_rs_rq in H10; [|left; reflexivity].
          destruct H10 as [rcidx [down ?]]; dest.
          simpl in *.
          inv H6; repeat disc_RqRsMsgFrom.
          do 3 eexists.
          repeat ssplit; [left; reflexivity| | |]; try eassumption.
        }
        destruct H14 as [rcidx [rsUp [rsum ?]]]; dest.
        destruct H.
        eapply inside_parent_in; try eapply H; try eassumption.
        intro Hx; subst.
        disc_rule_conds; auto.

    - disc_rule_conds.
      pose proof (edgeDownTo_Some H _ H34).
      destruct H.
      destruct H6 as [rqUp [rsUp [rpidx ?]]]; dest.
      disc_RqRsMsgFrom.
      eapply inside_child_in in H25; try eassumption.
  Qed.

  Lemma step_separation_outside_ok:
    forall soidx oidx,
      oidx <> soidx ->
      forall st1 st2 ridx rins routs,
        Reachable (steps step_m) sys st1 ->
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        Forall
          (fun eout =>
             exists oidx,
               RqRsMsgFrom oidx eout /\
               ~ In oidx (subtreeIndsOf dtr soidx)) rins ->
        ~ In oidx (subtreeIndsOf dtr soidx).
  Proof.
    destruct Hrrs as [? [? ?]].
    intros.
    pose proof (footprints_ok H0 H3).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      destruct H.
      eapply outside_parent_out in H5; try eassumption.
    - disc_rule_conds.
      pose proof (edgeDownTo_Some H _ H25).
      destruct H.
      destruct H7 as [rqUp [rsUp [rpidx ?]]]; dest.
      disc_rule_conds.
      eapply outside_child_in in H5; try eassumption.
      clear -H2 H5; firstorder.

    - disc_rule_conds.
      + destruct H; eapply outside_parent_out in H16; try eassumption.
      + destruct H; eapply outside_parent_out in H7; try eassumption.
      + pose proof (edgeDownTo_Some H _ H4).
        destruct H.
        destruct H13 as [rqUp [rsUp [rpidx ?]]]; dest.
        disc_rule_conds.
        eapply outside_child_in in H9; try eassumption.
        clear -H2 H9; firstorder.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + pose proof (edgeDownTo_Some H _ H10).
        destruct H27 as [rqUp [rsUp [rpidx ?]]]; dest.
        destruct H.
        disc_rule_conds.
        eapply outside_child_in in H26; try eassumption.
        clear -H2 H26; firstorder.
      + assert (exists rcidx rsUp rsm,
                   In (rsUp, rsm) rins /\
                   parentIdxOf dtr rcidx = Some (obj_idx obj) /\
                   rsEdgeUpFrom dtr rcidx = Some rsUp /\
                   ~ In rcidx (subtreeIndsOf dtr soidx)).
        { rewrite <-H31 in H24.
          pose proof (RqRsDownMatch_rs_not_nil H24).
          destruct rins as [|[rmidx rmsg] rins]; [exfalso; auto|].
          eapply RqRsDownMatch_rs_rq in H24; [|left; reflexivity].
          destruct H24 as [rcidx [down ?]]; dest.
          simpl in *.
          inv H5; repeat disc_RqRsMsgFrom.
          do 3 eexists.
          repeat ssplit; [left; reflexivity| | |]; try eassumption.
        }
        destruct H8 as [rcidx [rsUp [rsum ?]]]; dest.
        destruct H.
        eapply outside_parent_out in H29; try eassumption.
      + assert (exists rcidx rsUp rsm,
                   In (rsUp, rsm) rins /\
                   parentIdxOf dtr rcidx = Some (obj_idx obj) /\
                   rsEdgeUpFrom dtr rcidx = Some rsUp /\
                   ~ In rcidx (subtreeIndsOf dtr soidx)).
        { rewrite <-H31 in H9.
          pose proof (RqRsDownMatch_rs_not_nil H9).
          destruct rins as [|[rmidx rmsg] rins]; [exfalso; auto|].
          eapply RqRsDownMatch_rs_rq in H9; [|left; reflexivity].
          destruct H9 as [rcidx [down ?]]; dest.
          simpl in *.
          inv H5; repeat disc_RqRsMsgFrom.
          do 3 eexists.
          repeat ssplit; [left; reflexivity| | |]; try eassumption.
        }
        destruct H13 as [rcidx [rsUp [rsum ?]]]; dest.
        destruct H.
        eapply outside_parent_out in H25; try eassumption.

    - disc_rule_conds.
      pose proof (edgeDownTo_Some H _ H33).
      destruct H.
      destruct H5 as [rqUp [rsUp [rpidx ?]]]; dest.
      disc_rule_conds.
      eapply outside_child_in in H24; try eassumption.
      clear -H2 H24; firstorder.
  Qed.
  
  Lemma atomic_separation_ok:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall soidx,
          ~ In soidx (oindsOf hst) ->
          (exists cidx,
              parentIdxOf dtr cidx = Some soidx /\
              SubList (oindsOf hst) (subtreeIndsOf dtr cidx)) \/
          DisjList (oindsOf hst) (subtreeIndsOf dtr soidx).
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst.
    - destruct (in_dec eq_nat_dec oidx (subtreeIndsOf dtr soidx)).
      + left.
        destruct H.
        eapply subtreeIndsOf_composed in i; [|assumption].
        destruct i; subst; [intuition idtac|].
        destruct H6 as [cidx [? ?]].
        exists cidx; split; auto.
        apply SubList_cons; [assumption|apply SubList_nil].
      + right; apply (DisjList_singleton_1 eq_nat_dec); assumption.
    - inv_steps.
      assert (oidx <> soidx /\ ~ In soidx (oindsOf hst)) by intuition idtac.
      dest.
      specialize (IHAtomic _ _ H8 H11 _ H6).
      destruct IHAtomic.
      + destruct H7 as [cidx ?]; dest.
        pose proof (atomic_ext_outs_bounded H2 H8 H11 H9).
        left; exists cidx.
        split; [assumption|].
        apply SubList_cons; [|assumption].
        eapply SubList_forall in H12; [|eassumption].
        assert (Reachable (steps step_m) sys st2) by eauto.
        eapply step_separation_inside_child_ok; eauto.
      + pose proof (atomic_msg_outs_disj H2 H8 H11 H7).
        right.
        apply (DisjList_cons_inv eq_nat_dec); [assumption|].
        specialize (H7 oidx); destruct H7; [|assumption].
        eapply SubList_forall in H9; [|eassumption].
        assert (Reachable (steps step_m) sys st2) by eauto.
        eapply step_separation_outside_ok; eauto.
  Qed.

  (** This lemma is a bit freaky but crucially used in the proof of 
   * the coverage invariant.
   *)
  Lemma atomic_non_visiting_rsUps_one:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall ruTo rsUps,
          ~ In ruTo (oindsOf hst) ->
          rsUps <> nil ->
          NoDup (idsOf rsUps) ->
          Forall (fun msg =>
                    exists cidx,
                      parentIdxOf dtr cidx = Some ruTo /\
                      rsEdgeUpFrom dtr cidx = Some (idOf msg)) rsUps ->
          SubList rsUps eouts ->
          exists cidx rsUp,
            rsUps = [rsUp] /\
            rsEdgeUpFrom dtr cidx = Some (idOf rsUp) /\
            SubList (oindsOf hst) (subtreeIndsOf dtr cidx).
  Proof.
    intros.
    
    destruct rsUps as [|[rsUp0 rsm0] rsUps]; [exfalso; auto|].
    destruct rsUps as [|[rsUp1 rsm1] rsUps].

    - inv H5; clear H10.
      destruct H9 as [cidx [? ?]].
      apply SubList_cons_inv in H6; dest; clear H8.
      pose proof (atomic_ext_outs_in_history H H0 H1).
      rewrite Forall_forall in H8.
      apply H8 in H6; destruct H6 as [oidx0 [? ?]].
      repeat disc_RqRsMsgFrom.
      
      eapply atomic_separation_ok in H; try eassumption.
      destruct H.
      + destruct H as [rcidx [? ?]].
        destruct (eq_nat_dec cidx rcidx); subst.
        * disc_rule_conds; eauto.
        * exfalso.
          apply H6 in H9.
          eapply subtreeIndsOf_other_child_not_in;
            try eapply Hrrs; try eassumption.
      + exfalso.
        specialize (H cidx).
        destruct H; [auto|].
        elim H.
        apply subtreeIndsOf_child_in; try eapply Hrrs; try assumption.

    - exfalso; clear H3.
      assert (rsUp0 <> rsUp1).
      { inv H4; inv H9.
        intro Hx; elim H8.
        unfold idOf in Hx; rewrite Hx.
        left; reflexivity.
      }
      clear H4.
      apply SubList_cons_inv in H6; dest.
      apply SubList_cons_inv in H6; dest.
      clear H7.
      inv H5; inv H10; clear H11.
      destruct H9 as [cidx0 [? ?]].
      destruct H8 as [cidx1 [? ?]].
      simpl in *.
      assert (cidx0 <> cidx1)
        by (intro Hx; subst; repeat disc_rule_minds; auto).

      pose proof (atomic_ext_outs_in_history H H0 H1).
      rewrite Forall_forall in H11.
      apply H11 in H4; destruct H4 as [oidx0 [? ?]].
      apply H11 in H6; destruct H6 as [oidx1 [? ?]].
      clear H11.
      repeat disc_RqRsMsgFrom.

      eapply atomic_separation_ok in H; try eassumption.
      destruct H.
      + destruct H as [cidx [? ?]].
        destruct (eq_nat_dec cidx cidx0); subst.
        * apply H4 in H13.
          destruct Hrrs as [[? _] _].
          generalize H13.
          eapply subtreeIndsOf_other_child_not_in; try eassumption.
          congruence.
        * apply H4 in H12.
          destruct Hrrs as [[? _] _].
          generalize H12.
          eapply subtreeIndsOf_other_child_not_in; try eassumption.
          congruence.
      + specialize (H cidx0).
        destruct H; [auto|].
        elim H.
        destruct Hrrs as [[? _] _].
        apply subtreeIndsOf_child_in; assumption.
  Qed.

  Corollary atomic_non_visiting_rsUp_one:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall ruTo cidx rsUp,
          ~ In ruTo (oindsOf hst) ->
          parentIdxOf dtr cidx = Some ruTo ->
          rsEdgeUpFrom dtr cidx = Some (idOf rsUp) ->
          In rsUp eouts ->
          SubList (oindsOf hst) (subtreeIndsOf dtr cidx).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    eapply atomic_non_visiting_rsUps_one with (rsUps:= [rsUp]) in H2;
      try eassumption.
    - destruct H2 as [rcidx [rrsUp ?]]; dest.
      inv H2; disc_rule_minds.
      assumption.
    - discriminate.
    - repeat constructor; auto.
    - repeat constructor; eauto.
    - red; intros; dest_in; assumption.
  Qed.

End Separation.

Ltac disc_RqRsMsgFrom :=
  match goal with
  | [H: exists _, RqRsMsgFrom _ _ _ /\ _ |- _] =>
    let oidx := fresh "oidx" in
    destruct H as [oidx [? ?]]
  | [H0: RqRsSys _ _,
     H1: rqEdgeUpFrom _ ?oidx1 = Some ?rqUp,
     H2: RqRsMsgFrom _ ?oidx2 (?rqUp, _) |- _] =>
    eapply RqRsMsgFrom_rqEdgeUpFrom_eq in H2; [|eapply H0|eapply H1]; subst
  | [H0: RqRsSys _ _,
     H1: rsEdgeUpFrom _ ?oidx1 = Some ?rsUp,
     H2: RqRsMsgFrom _ ?oidx2 (?rsUp, _) |- _] =>
    eapply RqRsMsgFrom_rsEdgeUpFrom_eq in H2; [|eapply H0|eapply H1]; subst
  | [H0: RqRsSys _ _,
     H1: edgeDownTo _ ?cidx = Some ?down,
     H2: parentIdxOf _ ?cidx = Some ?oidx1,
     H3: RqRsMsgFrom _ ?oidx2 (?down, _) |- _] =>
    eapply RqRsMsgFrom_edgeDownTo_eq in H3;
    [|eapply H0|eapply H1|eapply H2]; subst
  end.

Ltac disc_RqRsMsgTo :=
  match goal with
  | [H: exists _, RqRsMsgTo _ _ _ /\ _ |- _] =>
    let oidx := fresh "oidx" in
    destruct H as [oidx [? ?]]
  | [H0: RqRsSys _ _,
     H1: parentIdxOf _ ?cidx = Some ?oidx1,
     H2: rqEdgeUpFrom _ ?cidx = Some ?rqUp,
     H3: RqRsMsgTo _ ?oidx2 (?rqUp, _) |- _] =>
    eapply RqRsMsgTo_rqEdgeUpFrom_eq in H3;
    [|eapply H0|eapply H1|eapply H2]; subst
  | [H0: RqRsSys _ _,
     H1: parentIdxOf _ ?cidx = Some ?oidx1,
     H2: rsEdgeUpFrom _ ?oidx1 = Some ?rsUp,
     H3: RqRsMsgTo _ ?oidx2 (?rsUp, _) |- _] =>
    eapply RqRsMsgTo_rsEdgeUpFrom_eq in H3;
    [|eapply H0|eapply H1|eapply H2]; subst
  | [H0: RqRsSys _ _,
     H1: edgeDownTo _ ?cidx = Some ?down,
     H2: RqRsMsgTo _ ?oidx2 (?down, _) |- _] =>
    eapply RqRsMsgTo_edgeDownTo_eq in H2;
    [|eapply H0|eapply H1]; subst
  end.

Close Scope list.
Close Scope fmap.

