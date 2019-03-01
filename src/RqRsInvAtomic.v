Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvMsg RqRsInvLock.
Require Import RqUpRed.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Definition lastOIdxOf (hst: MHistory): option IdxT :=
  match hst with
  | RlblInt oidx _ _ _ :: _ => Some oidx
  | _ => None
  end.

Definition oidxOf (lbl: MLabel) :=
  match lbl with
  | RlblInt oidx _ _ _ => Some oidx
  | _ => None
  end.

Fixpoint oindsOf (hst: MHistory) :=
  match hst with
  | nil => nil
  | lbl :: hst' => (oidxOf lbl) ::> (oindsOf hst')
  end.

Lemma atomic_lastOIdxOf:
  forall inits ins hst outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
    exists loidx,
      lastOIdxOf hst = Some loidx.
Proof.
  induction 1; simpl; intros; eauto.
Qed.

Lemma steps_object_in_system:
  forall {oifc} (sys: System oifc) st1 hst st2,
    steps step_m sys st1 hst st2 ->
    forall oidx,
      In oidx (oindsOf hst) ->
      exists obj,
        In obj sys.(sys_objs) /\
        obj.(obj_idx) = oidx.
Proof.
  induction 1; simpl; intros; [exfalso; auto|].
  destruct lbl; simpl in *; auto.
  destruct H1; subst; auto.
  inv_step.
  exists obj; auto.
Qed.

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
               (nhst = nil \/
                (exists nins nouts, Atomic msg_dec rqUps nins nhst nouts routs)))) /\
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
        * right; do 2 eexists.
          econstructor.
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
          { right; do 2 eexists.
            econstructor.
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
             (nhst = nil \/
              exists nins nouts, Atomic msg_dec rqUps nins nhst nouts eouts)) /\
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
          econstructor.
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
        destruct H9; subst.

        * simpl in *.
          pose proof (atomic_unique H2 H6); dest; subst; clear H2.
          red in H5; destruct H5 as [cidx [rqUp ?]]; dest; subst.
          assert (rins = [rqUp]); subst.
          { inv_step; inv H23.
            destruct rins; [elim H3; reflexivity|].
            pose proof (H4 i (or_introl eq_refl)); Common.dest_in.
            destruct rins; [reflexivity|].
            specialize (H4 i0 (or_intror (or_introl eq_refl))); Common.dest_in.
            red in H12; simpl in H12.
            inv H12; elim H15; left; reflexivity.
          }
          pose proof (reachable_steps H8 H10).
          rewrite removeL_nil; simpl.
          eapply rqUp_start_ok_end; eauto.

        * destruct H9 as [pnins [pnouts ?]].
          exists pruhst, (RlblInt oidx ridx rins routs :: pnhst).
          repeat ssplit.
          { reflexivity. }
          { right; exists roidx, rqUps, ruins, ruouts.
            repeat ssplit; try assumption.
            right; do 2 eexists.
            econstructor; eauto.
          }
          { constructor; [|assumption].
            assert (Reachable (steps step_m) sys st3) by eauto.
            eapply steps_split in H10; [|reflexivity].
            destruct H10 as [sti [? ?]].
            eapply nonRqUpL_atomic_msg_outs_no_rqUp in H9;
              [|assumption
               |eapply reachable_steps; [|eapply H10]; assumption
               |eassumption].
            eapply SubList_forall in H4; [|eassumption].
            eapply nonRqUp_ins_nonRqUpL; try eapply H12; eauto.
          }
  Qed.

End RqUpStart.

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

  Lemma atomic_msg_outs_bounded:
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

  Corollary atomic_msg_outs_in_history:
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
    eapply atomic_msg_outs_bounded in H; try eassumption.
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
    eapply atomic_msg_outs_in_history in H; try eassumption.
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
    eapply atomic_msg_outs_in_history in H; try eassumption.
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
    eapply atomic_msg_outs_in_history in H; try eassumption.
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
      + destruct i as [midx msg]; simpl in *.
        pose proof (edgeDownTo_Some H _ H11).
        destruct H21 as [rqUp [rsUp [rpidx ?]]]; dest.
        destruct H.
        disc_RqRsMsgFrom.
        eapply inside_child_in in H28; try eassumption.
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
      + destruct i as [midx msg]; simpl in *.
        pose proof (edgeDownTo_Some H _ H10).
        destruct H20 as [rqUp [rsUp [rpidx ?]]]; dest.
        destruct H.
        disc_rule_conds.
        eapply outside_child_in in H27; try eassumption.
        clear -H2 H27; firstorder.
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
        pose proof (atomic_msg_outs_bounded H2 H8 H11 H9).
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
      pose proof (atomic_msg_outs_in_history H H0 H1).
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

      pose proof (atomic_msg_outs_in_history H H0 H1).
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
    - red; intros; Common.dest_in; assumption.
  Qed.

End Separation.

Section MsgOutCases.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypothesis (Hrrs: RqRsSys dtr sys).

  Definition RsDownMsgTo (oidx: IdxT) (idm: Id Msg) :=
    msg_type (valOf idm) = MRs /\
    edgeDownTo dtr oidx = Some (idOf idm).

  Definition RqDownMsgTo (oidx: IdxT) (idm: Id Msg) :=
    msg_type (valOf idm) = MRq /\
    edgeDownTo dtr oidx = Some (idOf idm).

  Definition RsUpMsgFrom (oidx: IdxT) (idm: Id Msg) :=
    msg_type (valOf idm) = MRs /\
    rsEdgeUpFrom dtr oidx = Some (idOf idm).

  Ltac disc_msg_case :=
    match goal with
    | [H: RsDownMsgTo _ _ |- _] => destruct H
    | [H: RqDownMsgTo _ _ |- _] => destruct H
    | [H: RsUpMsgFrom _ _ |- _] => destruct H
    end.

  Definition NoDownLock (oidx: IdxT) (orqs: ORqs Msg) :=
    orqs@[oidx] >>=[True] (fun orq => orq@[downRq] = None).

  Definition NoDownLocks (oinds: list IdxT) (orqs: ORqs Msg) :=
    forall oidx,
      In oidx oinds -> NoDownLock oidx orqs.

  Definition NoDownLocks2 (oinds1: list IdxT) (oinds2: list IdxT) (orqs: ORqs Msg) :=
    forall oidx,
      In oidx oinds1 ->
      In oidx oinds2 ->
      NoDownLock oidx orqs.

  Definition HistoryInTree (ridx: IdxT) (hst: MHistory) :=
    SubList (oindsOf hst) (subtreeIndsOf dtr ridx).

  Definition HistoryDisjTree (ridx: IdxT) (hst: MHistory) :=
    DisjList (oindsOf hst) (subtreeIndsOf dtr ridx).

  Definition RsDownMsgOutInv (oidx: IdxT) (rsDown: Id Msg) (hst: MHistory) :=
    RsDownMsgTo oidx rsDown /\
    HistoryDisjTree oidx hst.

  Definition RqDownMsgOutInv (oidx: IdxT) (rqDown: Id Msg) (hst: MHistory) :=
    RqDownMsgTo oidx rqDown /\
    HistoryDisjTree oidx hst.

  Definition RsUpMsgOutInv (oidx: IdxT) (rsUp: Id Msg) (orqs: ORqs Msg) (hst: MHistory) :=
    RsUpMsgFrom oidx rsUp /\
    NoDownLocks2 (oindsOf hst) (subtreeIndsOf dtr oidx) orqs.

  Definition DownLockCoverInv (oidx: IdxT) (rqid: RqInfo Msg) (hst: MHistory) :=
    forall cidx rsUp,
      parentIdxOf dtr cidx = Some oidx ->
      rsEdgeUpFrom dtr cidx = Some rsUp ->
      ~ In rsUp rqid.(rqi_minds_rss) ->
      HistoryDisjTree cidx hst.

  Definition DownLocksCoverInv (orqs: ORqs Msg) (hst: MHistory) :=
    forall oidx orq rqid,
      In oidx (oindsOf hst) ->
      orqs@[oidx] = Some orq ->
      orq@[downRq] = Some rqid ->
      DownLockCoverInv oidx rqid hst.

  Definition DownLockInRoot (roidx: IdxT) (orqs: ORqs Msg) (hst: MHistory) :=
    forall sidx sorq srqid,
      In sidx (oindsOf hst) ->
      orqs@[sidx] = Some sorq ->
      sorq@[downRq] = Some srqid ->
      In sidx (subtreeIndsOf dtr roidx).
  
  Definition DownLockRootInv (orqs: ORqs Msg) (hst: MHistory) :=
    forall roidx rorq rrqid rcidx rrsUp,
      In roidx (oindsOf hst) ->
      orqs@[roidx] = Some rorq ->
      rorq@[downRq] = Some rrqid ->
      parentIdxOf dtr rcidx = Some roidx ->
      edgeDownTo dtr rcidx = Some (rrqid.(rqi_midx_rsb)) ->
      rsEdgeUpFrom dtr rcidx = Some rrsUp ->
      ~ In rrsUp rrqid.(rqi_minds_rss) /\
      HistoryDisjTree rcidx hst /\
      DownLockInRoot roidx orqs hst.

  Definition DownLockNorm (orq: ORq Msg): nat :=
    orq@[downRq] >>=[0] (fun rqid => List.length rqid.(rqi_minds_rss) - 1).

  Fixpoint DownLocksNorm (oinds: list IdxT) (orqs: ORqs Msg): nat :=
    match oinds with
    | nil => 0
    | hoind :: toinds =>
      (orqs@[hoind] >>=[0] (fun orq => DownLockNorm orq)) +
      DownLocksNorm toinds orqs
    end.

  Definition MsgOutsNormInv (orqs: ORqs Msg) (hst: MHistory) (eouts: list (Id Msg)) :=
    List.length (idsOf eouts) = DownLocksNorm (oindsOf hst) orqs + 1.
  
  Inductive MsgOutsCases (orqs: ORqs Msg) (hst: MHistory): list (Id Msg) -> Prop :=
  | MsgOutsRsDown: (* Only one live RsDown message *)
      forall oidx rsDown,
        RsDownMsgOutInv oidx rsDown hst ->
        NoDownLocks (oindsOf hst) orqs ->
        MsgOutsCases orqs hst [rsDown]
  | MsgOutsRqDownRsUp: (* RqDown or RsUp messages *)
      forall eouts,
        NoDup (idsOf eouts) ->
        Forall (fun eout =>
                  exists oidx,
                    RqDownMsgOutInv oidx eout hst \/
                    RsUpMsgOutInv oidx eout orqs hst) eouts ->
        DownLocksCoverInv orqs hst ->
        DownLockRootInv orqs hst ->
        MsgOutsNormInv orqs hst eouts ->

        (** Currently I don't think we explicitly need to state all RqDown/RsUp
         * subtrees are disjoint to each other -- we can prove this using 
         * their respective invariants and the Up/DownLock invariants (already
         * proven in [RqRsInvLock.v]).
         *)
        MsgOutsCases orqs hst eouts.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_messages_in;
    try disc_msg_case.

  Ltac solve_msg_out_cases_step :=
    match goal with
    | [H: edgeDownTo _ _ = Some ?midx
       |- RqDownMsgOutInv _ (?midx, _) _ \/
          RsUpMsgOutInv _ (?midx, _) _ _] => left
    | [H: rsEdgeUpFrom _ _ = Some ?midx
       |- RqDownMsgOutInv _ (?midx, _) _ \/
          RsUpMsgOutInv _ (?midx, _) _ _] => right
    | [ |- RsDownMsgOutInv _ _ _] => split
    | [ |- RqDownMsgOutInv _ _ _] => split
    | [ |- RsUpMsgOutInv _ _ _ _] => split
                                       
    | [ |- DownLocksCoverInv _ _] => red; intros
    | [ |- DownLockCoverInv _ _ _] => red; intros
    | [ |- DownLockRootInv _ _] => red; intros; repeat ssplit
    | [ |- DownLockInRoot _ _ _] => red; intros

    | [ |- MsgOutsNormInv _ _ _] => red; simpl

    | [ |- RqDownMsgTo _ _] => red; eauto; fail
    | [ |- RsDownMsgTo _ _] => red; eauto; fail
    | [ |- RsUpMsgFrom _ _] => red; eauto; fail

    | [ |- HistoryDisjTree _ _] => red; simpl
    | [ |- NoDownLocks _ _] => simpl; red; intros
    | [ |- NoDownLock _ _] => red; repeat (mred; simpl); fail
    | [ |- NoDownLocks2 _ _ _] => simpl; red; intros

    | [H: In _ [_] |- _] => Common.dest_in
    | [H: In _ (oindsOf [_]) |- _] => Common.dest_in
    | [ |- DisjList [_] _] => apply (DisjList_singleton_1 eq_nat_dec)
    | [H: parentIdxOf _ ?cidx = Some ?pidx
       |- ~ In ?pidx (subtreeIndsOf _ ?cidx)] =>
      apply parent_not_in_subtree; assumption
    | [ |- Forall _ _] => repeat constructor
    | [ |- NoDup _] => clear; simpl; repeat constructor; firstorder; fail
    | [ |- exists _, _] => eexists
    | [ |- context [(Some _) >>=[_] (fun _ => _)]] => simpl
    end.

  Ltac solve_msg_out_cases :=
    repeat (try solve_msg_out_cases_step; mred).

  Ltac solve_msg_out_cases_bt :=
    try (solve_msg_out_cases; fail).

  Lemma step_msg_outs_ok:
    forall st1 st2 oidx ridx rins routs,
      Reachable (steps step_m) sys st1 ->
      NonRqUpL dtr (RlblInt oidx ridx rins routs) ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      MsgOutsCases st2.(bst_orqs) [RlblInt oidx ridx rins routs] routs.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H2).
    inv_step.
    good_rqrs_rule_get rule.
    pose proof H; destruct H6 as [? _].
    good_rqrs_rule_cases rule; simpl in *.

    - disc_rule_conds.
      eapply MsgOutsRsDown; solve_msg_out_cases.

    - disc_rule_conds.
      eapply MsgOutsRqDownRsUp; solve_msg_out_cases.
      unfold DownLockNorm; mred.

    - disc_rule_conds.
      + exfalso.
        pose proof (rqEdgeUpFrom_Some H _ H8).
        destruct H15 as [rsUp [down [pidx ?]]]; dest.
        repeat disc_rule_minds.
        elim (H3 pidx).
        do 2 eexists; eauto.
      + eapply MsgOutsRqDownRsUp; solve_msg_out_cases.
        * destruct H20; assumption.
        * apply Forall_forall; intros [midx msg] ?.
          rewrite Forall_forall in H34; specialize (H34 _ H7).
          apply in_map with (f:= idOf) in H7.
          eapply RqRsDownMatch_rq_rs in H23; [|eassumption].
          destruct H23 as [cidx [rsUp ?]]; dest.
          eexists; left.
          solve_msg_out_cases.
        * intro Hx.
          eapply RqRsDownMatch_rs_rq in H23; [|eassumption].
          destruct H23 as [cidx [down ?]]; dest.
          disc_rule_conds; auto.
        * eapply parent_subtreeIndsOf_self_in;
            [destruct H; assumption|eassumption].
        * unfold DownLockNorm; mred; simpl.
          red in H23; dest.
          assert (length (idsOf routs) > 0)
            by (destruct (idsOf routs); simpl; [exfalso; auto|omega]).
          omega.
      + eapply MsgOutsRqDownRsUp; solve_msg_out_cases.
        * destruct H20; assumption.
        * apply Forall_forall; intros [midx msg] ?.
          rewrite Forall_forall in H34; specialize (H34 _ H9).
          apply in_map with (f:= idOf) in H9.
          eapply RqRsDownMatch_rq_rs in H8; [|eassumption].
          destruct H8 as [cidx [rsUp ?]]; dest.
          eexists; left.
          solve_msg_out_cases.
        * solve_midx_false.
        * solve_midx_false.
        * unfold DownLockNorm; mred; simpl.
          red in H8; dest.
          assert (length (idsOf routs) > 0)
            by (destruct (idsOf routs); simpl; [exfalso; auto|omega]).
          omega.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + eapply MsgOutsRsDown; solve_msg_out_cases.
      + eapply MsgOutsRsDown; solve_msg_out_cases.
      + eapply MsgOutsRqDownRsUp; solve_msg_out_cases.
        unfold DownLockNorm; mred.

    - disc_rule_conds.
      eapply MsgOutsRqDownRsUp; solve_msg_out_cases.
      + destruct H20; assumption.
      + apply Forall_forall; intros [midx msg] ?.
        rewrite Forall_forall in H29; specialize (H29 _ H7).
        apply in_map with (f:= idOf) in H7.
        eapply RqRsDownMatch_rq_rs in H23; [|eassumption].
        destruct H23 as [cidx [rsUp ?]]; dest.
        eexists; left.
        solve_msg_out_cases.
      + intro Hx.
        eapply RqRsDownMatch_rs_rq in H23; [|eassumption].
        destruct H23 as [cidx [down ?]]; dest.
        disc_rule_conds; auto.
      + apply edgeDownTo_subtreeIndsOf_self_in;
          [destruct H; assumption|congruence].
      + unfold DownLockNorm; mred; simpl.
        red in H23; dest.
        assert (length (idsOf routs) > 0)
          by (destruct (idsOf routs); simpl; [exfalso; auto|omega]).
        omega.
  Qed.

  Ltac inv_MsgOutsCases :=
    repeat
      match goal with
      | [H: SubList [_] _ |- _] => apply SubList_singleton_In in H
      | [H: In _ [_] |- _] => Common.dest_in
      | [H: MsgOutsCases _ _ _ |- _] => inv H
      | [H1: In _ ?eouts, H2: Forall _ ?eouts |- _] =>
        rewrite Forall_forall in H2;
        let oidx := fresh "oidx" in pose proof (H2 _ H1) as [oidx ?]
      | [H: RqDownMsgOutInv _ _ _ \/ RsUpMsgOutInv _ _ _ _ |- _] => destruct H
      | [H: RsDownMsgOutInv _ _ _ |- _] => destruct H
      | [H: RqDownMsgOutInv _ _ _ |- _] => destruct H
      | [H: RsUpMsgOutInv _ _ _ _ |- _] => destruct H
      | [H: RsDownMsgTo _ _ |- _] => disc_rule_conds; solve_midx_false; fail
      | [H: RqDownMsgTo _ _ |- _] => disc_rule_conds; solve_midx_false; fail
      | [H: RsUpMsgFrom _ _ |- _] => disc_rule_conds; solve_midx_false; fail
      end.

  Lemma rqDownMsgOutInv_no_rqDown:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall oidx rqdm,
          In rqdm eouts ->
          RqDownMsgOutInv oidx rqdm hst ->
          forall ooidx orqdm,
            RqDownMsgTo ooidx orqdm ->
            In orqdm eouts -> orqdm <> rqdm ->
            ~ In ooidx (subtreeIndsOf dtr oidx).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    destruct rqdm as [rqDown rqm].
    destruct orqdm as [orqDown orqm].
    disc_msg_case.
    pose proof (edgeDownTo_Some H _ H10).
    destruct H11 as [rqUp [rsUp [pidx ?]]]; dest.
    assert (In orqDown (idsOf eouts))
      by (apply in_map_iff; exists (orqDown, orqm); auto).
    pose proof (atomic_down_out_in_history
                  Hrrs H2 H3 H4 _ H10 H13 H14); clear H14.
    simpl in *.
    destruct H6 as [[? ?] ?]; simpl in *.
    pose proof (steps_object_in_system H4 _ H15).
    destruct H17 as [pobj [? ?]].

    intro Hx.
    eapply DisjList_In_2 in H15; [|eassumption].
    eapply inside_child_outside_parent_case in Hx;
      try eassumption; try apply Hrrs; subst.
    disc_rule_conds.

    pose proof (atomic_messages_eouts_in msg_dec H2 H4).
    rewrite Forall_forall in H10.
    pose proof (H10 _ H5).
    pose proof (H10 _ H8).
    
    pose proof (downLockInv_ok H0 H (reachable_steps H3 H4)).
    good_locking_get pobj.
    eapply downLockInvORq_down_rqsQ_length_two_False;
      try eassumption.
    eapply rqsQ_length_two;
      [eapply H6|eapply H7| | |]; eauto.
    intro Hx; subst; auto.
  Qed.

  Lemma rqDownMsgOutInv_no_rsUp:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall oidx rqdm,
          In rqdm eouts ->
          RqDownMsgOutInv oidx rqdm hst ->
          forall ooidx opidx opobj orsum,
            parentIdxOf dtr ooidx = Some opidx ->
            In opobj sys.(sys_objs) ->
            opobj.(obj_idx) = opidx ->
            RsUpMsgFrom ooidx orsum ->
            In orsum eouts ->
            ~ In opidx (subtreeIndsOf dtr oidx).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    destruct rqdm as [rqDown rqm].
    destruct orsum as [rsUp rsm].
    disc_msg_case.
    assert (In rsUp (idsOf eouts))
      by (apply in_map_iff; exists (rsUp, rsm); auto).
    pose proof (atomic_rsUp_out_in_history Hrrs H2 H3 H4 _ H12 H13); clear H13.
    simpl in *.
    destruct H6 as [[? ?] ?]; simpl in *.

    intro Hx.
    eapply inside_child_in in Hx; [|apply H|eassumption].
    specialize (H15 ooidx); destruct H15; auto.
  Qed.

  Lemma rsUpMsgOutInv_no_rqDown:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall oidx rsum,
          In rsum eouts ->
          RsUpMsgOutInv oidx rsum s2.(bst_orqs) hst ->
          forall ooidx orqdm,
            RqDownMsgTo ooidx orqdm ->
            In orqdm eouts ->
            ~ In ooidx (subtreeIndsOf dtr oidx).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    destruct rsum as [rsUp rsm].
    destruct orqdm as [orqDown orqm].
    disc_msg_case.
    pose proof (edgeDownTo_Some H _ H9).
    destruct H10 as [rqUp [rrsUp [pidx ?]]]; dest.
    assert (In orqDown (idsOf eouts))
      by (apply in_map_iff; exists (orqDown, orqm); auto).
    pose proof (atomic_down_out_in_history
                  Hrrs H2 H3 H4 _ H9 H12 H13); clear H13.
    simpl in *.
    destruct H6 as [[? ?] ?]; simpl in *.
    pose proof (steps_object_in_system H4 _ H14).
    destruct H16 as [pobj [? ?]].

    pose proof (atomic_messages_eouts_in msg_dec H2 H4).
    rewrite Forall_forall in H18.
    pose proof (H18 _ H5).
    pose proof (H18 _ H8).

    pose proof (downLockInv_ok H0 H (reachable_steps H3 H4)).
    good_locking_get pobj.

    intro Hx.
    destruct (eq_nat_dec ooidx oidx); subst.
    - eapply downLockInvORq_down_rqsQ_rsUp_False;
        try eapply H9; try eapply H13; try eassumption.
      + eapply rqsQ_length_ge_one; eauto.
      + eapply findQ_length_ge_one; eauto.
    - eapply inside_parent_in in Hx; try eassumption; [|apply Hrrs].
      specialize (H15 _ H14 Hx).
      eapply downLockInvORq_down_rqsQ_length_one_locked in H22;
        try eassumption.
      + destruct H22 as [rqid [? ?]].
        red in H15.
        destruct ((bst_orqs s2)@[obj_idx pobj]); simpl in *; [congruence|discriminate].
      + eapply rqsQ_length_ge_one; eauto.
  Qed.

  Lemma rsUpMsgOutInv_no_rsUp:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall oidx rsum,
          In rsum eouts ->
          RsUpMsgOutInv oidx rsum s2.(bst_orqs) hst ->
          forall ooidx opidx opobj orsum,
            parentIdxOf dtr ooidx = Some opidx ->
            In opobj sys.(sys_objs) ->
            opobj.(obj_idx) = opidx ->
            RsUpMsgFrom ooidx orsum ->
            In orsum eouts -> rsum <> orsum ->
            ~ In opidx (subtreeIndsOf dtr oidx).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    destruct rsum as [rsUp rsm].
    destruct orsum as [orsUp orsm].
    disc_msg_case.
    assert (In orsUp (idsOf eouts))
      by (apply in_map_iff; exists (orsUp, orsm); auto).
    pose proof (atomic_rsUp_out_in_history Hrrs H2 H3 H4 _ H13 H14); clear H14.
    simpl in *.
    destruct H6 as [[? ?] ?]; simpl in *.

    destruct (in_dec eq_nat_dec ooidx (subtreeIndsOf dtr oidx));
      [|eapply outside_parent_out; [apply H| |]; eassumption].

    pose proof (downLockInv_ok H0 H (reachable_steps H3 H4)).
    good_locking_get opobj.
    pose proof (atomic_messages_eouts_in msg_dec H2 H4).
    rewrite Forall_forall in H19.
    pose proof (H19 _ H5).
    pose proof (H19 _ H11).
    
    destruct (eq_nat_dec oidx ooidx); subst.
    - exfalso.
      disc_rule_conds.
      eapply downLockInvORq_rsUp_length_two_False in H18;
        try eassumption.
      eapply findQ_length_two; [|eapply H20|eapply H21].
      simpl; intro Hx; subst; auto.

    - destruct (in_dec eq_nat_dec (obj_idx opobj) (oindsOf hst)).
      + intro Hx.
        specialize (H16 _ i0 Hx); red in H16.
        eapply downLockInvORq_rsUp_length_one_locked in H18;
          try eassumption;
          [|eapply findQ_length_ge_one; eassumption].
        destruct H18 as [rqid ?]; dest.
        destruct ((bst_orqs s2)@[obj_idx opobj]); simpl in *;
          [congruence|discriminate].

      + exfalso.
        change orsUp with (idOf (orsUp, orsm)) in H13.
        pose proof (atomic_non_visiting_rsUp_one
                      Hrrs H2 H3 H4 _ _ n0 H7 H13 H11).
        assert (In rsUp (idsOf eouts))
          by (apply in_map_iff; exists (rsUp, rsm); auto).
        pose proof (atomic_rsUp_out_in_history
                      Hrrs H2 H3 H4 _ H14 H22); clear H22.
        apply H9 in H23.
        elim n.
        eapply subtreeIndsOf_In_each_other_eq;
          try eapply Hrrs; assumption.
  Qed.
    
  Lemma atomic_msg_outs_ok:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      Forall (NonRqUpL dtr) hst ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        MsgOutsCases s2.(bst_orqs) hst eouts.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst;
      [inv H2; inv_steps; eapply step_msg_outs_ok; eauto|].

    inv H8; inv_steps.
    specialize (IHAtomic H11 _ _ H9 H12); dest.

    assert (Reachable (steps step_m) sys st2) by eauto.
    pose proof (footprints_ok H0 H5) as Hftinv.
    pose proof (downLockInv_ok H0 H H5) as Hdlinv.
    pose proof (nonRqUpL_atomic_msg_outs_no_rqUp Hrrs H2 H11 H9 H12).
    eapply SubList_forall in H6; [|eassumption].

    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule; simpl in *.

    - (** [ImmDownRule]; exfalso *)
      disc_rule_conds.
      elim (H21 (obj_idx obj)).
      do 2 eexists; eauto.

    - (** [ImmUpRule] *)
      disc_rule_conds.
      replace (orqs+[obj_idx obj <- norq]) with orqs by meq.

      (* Several inversions *)
      (* - Invert [MsgOutsCases] to check whether the case is for the RsDown
       * message or RqDown/RsUp messages. *)
      inv_MsgOutsCases.

      (* - Collect some information about the current target output message. *)
      pose proof (edgeDownTo_Some H _ H30).
      destruct H32 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      assert (In rqFrom (idsOf eouts))
        by (apply in_map_iff; exists (rqFrom, rqm); auto).
      pose proof (atomic_down_out_in_history
                    Hrrs H2 H9 H12 _ H30 H34 H33); clear H33.

      eapply MsgOutsRqDownRsUp.
      + rewrite idsOf_app.
        apply NoDup_DisjList.
        * apply removeOnce_idsOf_NoDup; assumption.
        * repeat constructor; auto.
        * simpl; apply (DisjList_singleton_2 eq_nat_dec).
          intro Hx; apply removeOnce_idsOf_In in Hx.
          pose proof (atomic_rsUp_out_in_history
                        Hrrs H2 H9 H12 _ H36 Hx).
          specialize (H31 (obj_idx obj)).
          destruct H31; auto.
          elim H31.
          apply rsEdgeUpFrom_subtreeIndsOf_self_in;
            [apply Hrrs|congruence].
          
      + (* The invariant for each message *)
        apply Forall_app.
        * (* For the others except (rqFrom, rqm) *)
          apply Forall_forall.
          intros [midx msg] ?.
          apply removeOnce_In_NoDup in H33;
            [|apply idsOf_NoDup; assumption]; dest.

          pose proof (H8 _ H37).
          destruct H38 as [oidx ?].
          destruct H38.
          { (* RqDown *)
            exists oidx; left.
            destruct H38.
            split; [assumption|].
            red in H39.
            red; simpl.
            apply (DisjList_cons_inv eq_nat_dec); [assumption|].

            intro Hx.
            eapply DisjList_In_2 in H35; [|eassumption].
            eapply inside_child_outside_parent_case in Hx;
              try eassumption; try apply Hrrs; subst.
            disc_rule_conds.
            elim H33; f_equal.
            eapply idsOf_NoDup_In_value_eq; eauto.
          }
          { (* RsUp *)
            exists oidx; right.
            destruct H38.
            split; [assumption|].
            red; simpl; intros.
            destruct H40; [subst|auto].
            red; mred.
          }
          
        * (* For the new output *)
          repeat constructor.
          exists (obj_idx obj); right.
          split; [red; auto|].
          red; simpl; intros.
          destruct H33;
            [|specialize (H31 oidx); destruct H31; exfalso; auto].
          subst.
          red; mred.
          
      + red; simpl; intros.
        destruct H33; [subst; mred|].
        red; intros.
        red; simpl.
        apply (DisjList_cons_inv eq_nat_dec);
          [eapply H10; eauto|].
        intro Hx.

        specialize (H10 _ _ _ H33 H37 H38 _ _ H39 H40 H41).
        red in H10.
        eapply DisjList_In_2 in H35; [|eapply H10].
        eapply inside_child_outside_parent_case in Hx;
          try eassumption; try apply Hrrs; subst.

        pose proof (steps_object_in_system H12 _ H33).
        destruct H42 as [dobj [? ?]]; subst.
        good_locking_get dobj; mred.
        red in H43; mred.

        disc_rule_conds.
        specialize (H43 _ H34).
        destruct H43 as [down [rsUp ?]]; dest.
        disc_rule_conds.
        destruct (in_dec eq_nat_dec rsUp _); [auto|].
        red in H43; dest.
        eapply rqsQ_length_zero_False; eauto.
        
      + red; simpl; intros.
        destruct H33; [subst; mred|].
        pose proof (H14 _ _ _ _ _ H33 H37 H38 H39 H40 H41); dest.
        repeat ssplit; [assumption| |].
        * red in H43.
          red; simpl.
          apply (DisjList_cons_inv eq_nat_dec); [auto|].
          intro Hx.
          eapply DisjList_In_2 in H35; [|eassumption].
          eapply inside_child_outside_parent_case in Hx;
            try eassumption; try apply Hrrs; subst.
          disc_rule_conds.

          pose proof (steps_object_in_system H12 _ H33).
          destruct H39 as [robj [? ?]]; subst.
          good_locking_get robj; mred.
          red in H40; mred.
          specialize (H40 _ H34).
          destruct H40 as [down [rsUp' ?]]; dest.
          disc_rule_conds.
          destruct (in_dec eq_nat_dec rsUp' _); [auto|].
          red in H45; dest.
          eapply rqsQ_length_zero_False; eauto.
        * red; simpl; intros.
          destruct H45; [subst|eauto].
          mred.

      + red; repeat (simpl; mred).
        rewrite idsOf_app; simpl.
        rewrite app_length; simpl.
        unfold idsOf; rewrite map_length.
        apply (removeOnce_length (id_dec msg_dec)) in H4; dest.
        unfold Id in *; rewrite H33.
        unfold DownLockNorm; repeat (simpl; mred).
        red in H25.
        unfold idsOf in H25; rewrite map_length in H25.
        omega.
        
    - (** [RqFwdRule]; 
       * [RqUpUp] and [RqUpDown] cases are contradictory -- previous [eouts] 
       * cannot have any [RqUp] messages.
       * [RqDownDown] case is valid.
       *)
      disc_rule_conds;
        try (elim (H30 (obj_idx obj)); do 2 eexists; eauto; fail).

      inv_MsgOutsCases.
      pose proof (edgeDownTo_Some H _ H8).
      destruct H36 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      assert (In rqFrom (idsOf eouts))
        by (apply in_map_iff; exists (rqFrom, rqi_msg rqi); auto).
      pose proof (atomic_down_out_in_history
                    Hrrs H2 H9 H12 _ H8 H38 H37); clear H37.

      eapply MsgOutsRqDownRsUp.
      + rewrite idsOf_app.
        apply NoDup_DisjList.
        * apply removeOnce_idsOf_NoDup; assumption.
        * apply H26.
        * admit. (* [NoDup] for new output messages *)

      + apply Forall_app.
        * apply Forall_forall.
          intros [midx msg] ?.
          apply removeOnce_In_NoDup in H37;
            [|apply idsOf_NoDup; assumption]; dest.

          pose proof (H14 _ H41).
          destruct H42 as [oidx ?].
          destruct H42.
          { (* RqDown *)
            exists oidx; left.
            destruct H42.
            split; [assumption|].
            red in H43.
            red; simpl.
            apply (DisjList_cons_inv eq_nat_dec); [assumption|].

            intro Hx.
            eapply DisjList_In_2 in H43; [|eassumption].
            eapply inside_child_outside_parent_case in Hx;
              try eassumption; try apply Hrrs; subst.
            disc_rule_conds.
            elim H37; f_equal.
            eapply idsOf_NoDup_In_value_eq; eauto.
          }
          { (* RsUp *)
            exists oidx; right.
            destruct H42.
            split; [assumption|].

            pose proof (steps_object_in_system H12 _ H40).
            destruct H44 as [pobj [? ?]]; subst.
            good_locking_get pobj.
            
            assert (~ In (obj_idx pobj) (subtreeIndsOf dtr oidx)).
            { eapply downLockInvORq_down_rqsQ_length_one_locked in H45;
                try eassumption;
                [|eapply rqsQ_length_ge_one;
                  [eassumption|apply FirstMP_InMP; assumption]].
              destruct H45 as [rqid [? [? [rsUp [? ?]]]]].
              intro Hx.
              specialize (H43 _ H40 Hx).
              red in H43.
              destruct (orqs@[obj_idx pobj]); simpl in *;
                [congruence|discriminate].
            }
            
            assert (~ In (obj_idx obj) (subtreeIndsOf dtr oidx)).
            { intro Hx.
              eapply inside_child_outside_parent_case in H46;
                try eassumption; try apply Hrrs; subst.

              pose proof (atomic_messages_eouts_in msg_dec H2 H12).
              simpl in H46; rewrite Forall_forall in H46.
              pose proof (H46 _ H41).
              apply FirstMP_InMP in H31; simpl in H31.
              disc_rule_conds.

              eapply downLockInvORq_down_rqsQ_rsUp_False in H45;
                try eassumption.
              { eapply rqsQ_length_ge_one; eauto. }
              { eapply findQ_length_ge_one; eauto. }
            }

            red; simpl; intros.
            destruct H48.
            { subst; exfalso; auto. }
            { specialize (H43 _ H48 H49); red; mred. }
          }

        * apply Forall_forall.
          intros [rqTo rqm] ?.
          assert (In rqTo (idsOf routs))
            by (apply in_map_iff; exists (rqTo, rqm); auto).
          eapply RqRsDownMatch_rq_rs in H13; [|eassumption].
          destruct H13 as [cidx [rsUp ?]]; dest.
          rewrite Forall_forall in H39.
          pose proof (H39 _ H37); simpl in H46.
          exists cidx; left.
          split; [red; auto|].
          red in H34; red; simpl.
          apply (DisjList_cons_inv eq_nat_dec).
          { apply DisjList_comm in H34.
            eapply DisjList_comm, DisjList_SubList;
              [|eassumption].
            admit.
          }
          { apply parent_not_in_subtree; [apply Hrrs|auto]. }

      + red; simpl; intros.
        destruct (eq_nat_dec (obj_idx obj) oidx).
        * subst; mred.
          red; intros.
          red in H34; red; simpl.
          apply (DisjList_cons_inv eq_nat_dec).
          { admit. }
          { eapply parent_not_in_subtree; [apply Hrrs|auto]. }
        * destruct H37; [exfalso; auto|].
          mred; specialize (H18 _ _ _ H37 H41 H42).
          red; intros.
          specialize (H18 _ _ H43 H44 H45).
          red in H18.
          red; simpl; intros.
          apply (DisjList_cons_inv eq_nat_dec); [assumption|].

          (* obj_idx obj = cidx ... ditto *)
          admit.
          
      + admit.
      + admit.

    - (** [RsBackRule] *)
      good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + (** [RsDownDown] *)
        inv_MsgOutsCases.
        disc_rule_conds.
        destruct (id_dec msg_dec i i) as [_|]; [simpl|exfalso; auto].

        eapply MsgOutsRsDown.
        * split.
          { red; simpl; eauto. }
          { red; simpl.
            apply (DisjList_cons_inv eq_nat_dec).
            { red in H25; apply DisjList_comm in H25.
              eapply DisjList_comm, DisjList_SubList; [|eassumption].
              admit.
            }
            { apply parent_not_in_subtree; [apply Hrrs|assumption]. }
          }
        * red; simpl; intros.
          destruct H33; subst.
          { red; repeat (simpl; mred). }
          { specialize (H32 _ H33).
            red in H32; red.
            repeat (simpl; mred).
          }

      + (** [RsUpDown] *)
        inv_MsgOutsCases;
          [exfalso;
           eapply SubList_singleton_NoDup in H4;
            [|apply idsOf_NoDup, H22];
            destruct H4; [exfalso; auto|subst];
            rewrite <-H36 in H29;
            eapply RqRsDownMatch_rs_rq in H29; [|left; reflexivity];
            destruct H29 as [cidx [down ?]]; dest;
            disc_rule_conds;
            solve_midx_false|].
        admit.

      + (** [RsUpUp] *)
        admit.

    - (** [RsDownRqDownRule] *)
      disc_rule_conds.
      inv_MsgOutsCases.
      admit.
    
  Admitted.
  
End MsgOutCases.

Close Scope list.
Close Scope fmap.

