Require Import PeanoNat Lia List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvMsg RqRsInvLock RqRsInvSepO.
Require Import RqUpRed.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section Separation.
  Context `{dv: DecValue} `{oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System).
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (oinvs: IdxT -> ObjInv)
             (Hrrs: RqRsSys dtr sys oinvs).

  (*! Separation by an RqDown message *)

  Ltac disc_rule_custom ::=
    try disc_footprints_ok.

  Lemma step_rqDown_ins_outs_disj:
    forall cidx rqDown,
      edgeDownTo dtr cidx = Some (idOf rqDown) ->
      msg_type (valOf rqDown) = MRq ->
      forall st1 oidx ridx rins routs st2,
        Reachable (steps step_m) sys st1 ->
        InMPI (st_msgs st1) rqDown ->
        ~ In rqDown rins ->
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        ~ In rqDown routs.
  Proof.
    destruct Hrrs as [? [? [_ ?]]]; intros.
    assert (Reachable (steps step_m) sys st2).
    { eapply reachable_steps; [eassumption|].
      eapply steps_singleton; eassumption.
    }
    pose proof (downLockInv_ok Hiorqs H0 H H1 H8); clear H8.
    inv_step.
    good_locking_get obj.
    disc_rule_conds.
    intro Hx; destruct rqDown as [rqDown rsdm]; simpl in *.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
    - disc_rule_conds.
    - disc_rule_conds.
      + solve_midx_false.
      + solve_midx_false.

      + eapply RqRsDownMatch_rq_rs in H41;
          [|apply in_map with (f:= idOf) in Hx; simpl in Hx; eassumption].
        destruct H41 as [rcidx [rsUp ?]]; dest.
        repeat disc_rule_minds; subst.
        eapply downLockInvORq_down_rqsQ_length_two_False; try eassumption.
        destruct H23; solve_q.
        erewrite findQ_In_NoDup_enqMsgs by eassumption.
        rewrite filter_app; simpl.
        rewrite H3; simpl.
        rewrite app_length; simpl.
        eapply rqsQ_length_ge_one in H5; [|assumption].
        unfold rqsQ in H5; simpl in H5.
        lia.

      + eapply RqRsDownMatch_rq_rs in H26;
          [|apply in_map with (f:= idOf) in Hx; simpl in Hx; eassumption].
        destruct H26 as [rcidx [rsUp ?]]; dest.
        repeat disc_rule_minds; subst.
        eapply downLockInvORq_down_rqsQ_length_two_False; try eassumption.
        destruct H23; solve_q.
        erewrite findQ_In_NoDup_enqMsgs by eassumption.
        solve_q.
        rewrite filter_app; simpl.
        rewrite H3; simpl.
        rewrite app_length; simpl.
        eapply rqsQ_length_ge_one in H5; [|assumption].
        unfold rqsQ in H5; simpl in H5.
        lia.

      + eapply RqRsDownMatch_rq_rs in H11;
          [|apply in_map with (f:= idOf) in Hx; simpl in Hx; eassumption].
        destruct H11 as [rcidx [rsUp ?]]; dest.
        repeat disc_rule_minds; subst.
        eapply downLockInvORq_down_rqsQ_length_two_False; try eassumption.
        destruct H23; solve_q.
        erewrite findQ_In_NoDup_enqMsgs by eassumption.
        apply parentIdxOf_not_eq in H12; [|apply Hrrs].
        solve_q.
        rewrite filter_app; simpl.
        rewrite H3; simpl.
        rewrite app_length; simpl.
        eapply rqsQ_length_ge_one in H5; [|assumption].
        unfold rqsQ in H5; simpl in H5.
        lia.

    - disc_rule_conds.
    - disc_rule_conds.
      eapply RqRsDownMatch_rq_rs in H26;
        [|apply in_map with (f:= idOf) in Hx; simpl in Hx; eassumption].
      destruct H26 as [rcidx [rsUp ?]]; dest.
      repeat disc_rule_minds; subst.
      eapply downLockInvORq_down_rqsQ_length_two_False; try eassumption.
      assert (rqDown <> fst rsFrom).
      { intro; subst.
        eapply DisjList_In_2 in H25; [|left; reflexivity].
        apply in_map with (f:= idOf) in Hx; auto.
      }
      destruct H23; solve_q.
      erewrite findQ_In_NoDup_enqMsgs by eassumption.
      rewrite findQ_not_In_deqMP by assumption.
      apply parentIdxOf_not_eq in H26; [|apply Hrrs].
      solve_q.
      rewrite filter_app; simpl.
      rewrite H3; simpl.
      rewrite app_length; simpl.
      eapply rqsQ_length_ge_one in H5; [|assumption].
      unfold rqsQ in H5; simpl in H5.
      lia.
  Qed.

  Lemma atomic_rqDown_inits_outs_disj:
    forall cidx rqDown,
      edgeDownTo dtr cidx = Some (idOf rqDown) ->
      msg_type (valOf rqDown) = MRq ->
      forall inits ins hst outs eouts,
        Atomic inits ins hst outs eouts ->
        ~ In rqDown inits ->
        forall st1,
          Reachable (steps step_m) sys st1 ->
          InMPI (st_msgs st1) rqDown ->
          forall st2,
            steps step_m sys st1 hst st2 ->
            ~ In rqDown outs.
  Proof.
    induction 3; simpl; intros; subst.
    - inv_steps.
      eapply step_rqDown_ins_outs_disj; eauto.
    - inv_steps.
      specialize (IHAtomic H7 _ H8 H9 _ H11).
      intro Hx; apply in_app_or in Hx.
      destruct Hx; [auto|].
      eapply atomic_messages_in_in in H9; try eassumption.
      eapply step_rqDown_ins_outs_disj in H13; eauto.
      intro Hx; elim IHAtomic.
      eapply atomic_eouts_in; eauto.
  Qed.

  Corollary atomic_rqDown_inits_ins_disj:
    forall cidx rqDown,
      edgeDownTo dtr cidx = Some (idOf rqDown) ->
      msg_type (valOf rqDown) = MRq ->
      forall inits ins hst outs eouts,
        Atomic inits ins hst outs eouts ->
        ~ In rqDown inits ->
        forall st1,
          Reachable (steps step_m) sys st1 ->
          InMPI (st_msgs st1) rqDown ->
          forall st2,
            steps step_m sys st1 hst st2 ->
            ~ In rqDown ins.
  Proof.
    intros.
    pose proof H1.
    eapply atomic_rqDown_inits_outs_disj in H6; eauto.
    apply atomic_messages_ins_outs in H1.
    destruct H1.
    apply SubList_app_4 in H7.
    intro Hx; apply H7 in Hx.
    apply in_app_or in Hx; destruct Hx; auto.
  Qed.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_RqRsMsgFrom.

  Lemma step_rqDown_separation_inside_false:
    forall cidx rqDown pidx,
      parentIdxOf dtr cidx = Some pidx ->
      edgeDownTo dtr cidx = Some (idOf rqDown) ->
      msg_type (valOf rqDown) = MRq ->
      forall st1,
        Reachable (steps step_m) sys st1 ->
        InMPI (st_msgs st1) rqDown ->
        forall rins,
          Forall (fun rin =>
                    exists oidx,
                      RqRsMsgFrom dtr oidx rin /\
                      In oidx (subtreeIndsOf dtr cidx)) rins ->
          forall ridx routs st2,
            NonRqUpL dtr (RlblInt pidx ridx rins routs) ->
            step_m sys st1 (RlblInt pidx ridx rins routs) st2 ->
            False.
  Proof.
    destruct Hrrs as [? [? [_ ?]]]; intros.
    pose proof (footprints_ok Hiorqs H0 H5) as Hftinv.
    pose proof (downLockInv_ok Hiorqs H0 H H1 H5) as Hdlinv.
    inv_step.
    good_locking_get obj.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      + eapply downLockInvORq_down_rqsQ_length_one_locked in H9;
          try eassumption;
          [|eapply rqsQ_length_ge_one with (msg:= valOf rqDown); eassumption].
        dest; congruence.
      + destruct (idx_dec cidx cidx0); subst.
        * disc_rule_conds.
          eapply downLockInvORq_down_rqsQ_length_one_locked in H9;
            try eassumption;
            [|eapply rqsQ_length_ge_one with (msg:= valOf rqDown); eassumption].
          dest; congruence.
        * eapply subtreeIndsOf_child_disj in n; try eassumption; [|apply Hrrs].
          specialize (n cidx0); destruct n; auto.
          elim H7; eapply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
          congruence.

    - disc_rule_conds.
      pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H29).
      destruct H11 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      eapply parent_parent_in_False with (oidx2:= obj_idx obj);
        try apply Hrrs; eassumption.

    - disc_rule_conds.
      + pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H12).
        destruct H7 as [rqUp [rsUp [pidx ?]]]; dest.
        disc_rule_conds.
        elim (H8 pidx).
        do 2 eexists; repeat split; eauto.
      + pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H12).
        destruct H7 as [rqUp [rsUp [pidx ?]]]; dest.
        disc_rule_conds.
        elim (H8 pidx).
        do 2 eexists; repeat split; eauto.

      + eapply downLockInvORq_down_rqsQ_length_one_locked in H9;
          try eassumption;
          [|eapply rqsQ_length_ge_one with (msg:= valOf rqDown); eassumption].
          dest; congruence.
      + destruct (idx_dec (obj_idx upCObj) cidx); subst.
        * disc_rule_conds.
          eapply downLockInvORq_down_rqsQ_length_one_locked in H9;
            try eassumption;
            [|eapply rqsQ_length_ge_one with (msg:= valOf rqDown); eassumption].
          dest; congruence.
        * eapply subtreeIndsOf_child_disj in n; try eassumption; [|apply Hrrs].
          specialize (n (obj_idx upCObj)); destruct n; auto.
          elim H7; eapply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
          congruence.

      + pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H10).
        destruct H19 as [rqUp [rsUp [pidx ?]]]; dest.
        disc_rule_conds.
        eapply parent_parent_in_False with (oidx2:= obj_idx obj);
          try apply Hrrs; eassumption.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H13).
        destruct H32 as [rqUp [rsUp [pidx ?]]]; dest.
        disc_rule_conds.
        eapply parent_parent_in_False with (oidx1:= cidx) (oidx2:= obj_idx obj);
          try apply Hrrs; eassumption.
      + pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H13).
        destruct H28 as [rqUp [rsUp [pidx ?]]]; dest.
        disc_rule_conds.
        eapply parent_parent_in_False with (oidx1:= cidx) (oidx2:= obj_idx obj);
          try apply Hrrs; eassumption.

      + pose proof H9.
        red in H9; mred; dest.
        specialize (H31 _ H2).
        destruct H31 as [down [rsUp ?]]; dest.
        disc_rule_conds.
        destruct (in_dec idx_dec rsUp (map fst rqi.(rqi_rss))).
        * eapply RqRsDownMatch_rs_rq in H29; [|eassumption].
          destruct H29 as [rcidx [down ?]]; dest.
          disc_rule_conds.
          eapply downLockInvORq_down_rqsQ_rsUp_False
            with (cidx:= rcidx) in H13; try eassumption.
          { eapply rqsQ_length_ge_one; eassumption. }
          { rewrite <-H35 in i.
            apply in_map_iff in i; destruct i as [[rsUp' rsum] [? ?]].
            simpl in *; subst.
            rewrite Forall_forall in H19; specialize (H19 _ H36).
            eapply findQ_length_ge_one.
            apply FirstMP_InMP; eassumption.
          }
        * red in H34; dest.
          destruct rqDown as [rqDown rqdm]; simpl in *.
          pose proof (rqsQ_length_ge_one _ _ _ H4 H6).
          simpl in H37; rewrite H31 in H37.
          simpl in H37; lia.

      + pose proof H9.
        red in H9; mred; dest.
        specialize (H28 _ H2).
        destruct H28 as [down [rsUp ?]]; dest.
        disc_rule_conds.
        destruct (in_dec idx_dec rsUp (map fst rqi.(rqi_rss))).
        * eapply RqRsDownMatch_rs_rq in H16; [|eassumption].
          destruct H16 as [rcidx [down ?]]; dest.
          disc_rule_conds.
          eapply downLockInvORq_down_rqsQ_rsUp_False
            with (cidx:= rcidx) in H23; try eassumption.
          { eapply rqsQ_length_ge_one; eassumption. }
          { rewrite <-H35 in i.
            apply in_map_iff in i; destruct i as [[rsUp' rsum] [? ?]].
            simpl in *; subst.
            rewrite Forall_forall in H19; specialize (H19 _ H33).
            eapply findQ_length_ge_one.
            apply FirstMP_InMP; eassumption.
          }
        * red in H31; dest.
          destruct rqDown as [rqDown rqdm]; simpl in *.
          pose proof (rqsQ_length_ge_one _ _ _ H4 H6).
          simpl in H34; rewrite H28 in H34.
          simpl in H34; lia.

      + pose proof H9.
        red in H9; mred; dest.
        specialize (H16 _ H2).
        destruct H16 as [down [rsUp ?]]; dest.
        disc_rule_conds.
        destruct (in_dec idx_dec rsUp (map fst rqi.(rqi_rss))).
        * eapply RqRsDownMatch_rs_rq in H12; [|eassumption].
          destruct H12 as [rcidx [down ?]]; dest.
          disc_rule_conds.
          eapply downLockInvORq_down_rqsQ_rsUp_False
            with (cidx:= rcidx) in H13; try eassumption.
          { eapply rqsQ_length_ge_one; eassumption. }
          { rewrite <-H35 in i.
            apply in_map_iff in i; destruct i as [[rsUp' rsum] [? ?]].
            simpl in *; subst.
            rewrite Forall_forall in H19; specialize (H19 _ H28).
            eapply findQ_length_ge_one.
            apply FirstMP_InMP; eassumption.
          }
        * red in H27; dest.
          destruct rqDown as [rqDown rqdm]; simpl in *.
          pose proof (rqsQ_length_ge_one _ _ _ H4 H6).
          simpl in H29; rewrite H16 in H29.
          simpl in H29; lia.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H11).
      destruct H30 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      eapply parent_parent_in_False with (oidx1:= cidx) (oidx2:= obj_idx obj);
        try apply Hrrs; eassumption.
  Qed.

  Lemma step_rqDown_separation_outside_false:
    forall cidx pobj rqDown,
      In pobj sys.(sys_objs) ->
      parentIdxOf dtr cidx = Some (obj_idx pobj) ->
      edgeDownTo dtr cidx = Some (idOf rqDown) ->
      msg_type (valOf rqDown) = MRq ->
      forall st1,
        Reachable (steps step_m) sys st1 ->
        InMPI (st_msgs st1) rqDown ->
        forall rins (Hrins: rins <> nil),
          ~ In rqDown rins ->
          (forall rsDown,
              idOf rsDown = idOf rqDown ->
              msg_type (valOf rsDown) = MRs ->
              ~ In rsDown rins) ->
          Forall (fun rin =>
                    exists oidx,
                      RqRsMsgFrom dtr oidx rin /\
                      ~ In oidx (subtreeIndsOf dtr cidx)) rins ->
          forall ridx routs st2,
            NonRqUpL dtr (RlblInt cidx ridx rins routs) ->
            step_m sys st1 (RlblInt cidx ridx rins routs) st2 ->
            False.
  Proof.
    destruct Hrrs as [? [? [_ ?]]]; intros.
    pose proof (footprints_ok Hiorqs H0 H6) as Hftinv.
    pose proof (downLockInv_ok Hiorqs H0 H H1 H6) as Hdlinv.
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      elim H12; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].

    - disc_rule_conds.
      destruct rqDown as [rqDown rqdm]; simpl in *.
      assert (rqm <> rqdm) by (intro Hx; subst; elim H8; auto); clear H8.
      good_locking_get pobj.
      eapply downLockInvORq_down_rqsQ_length_two_False in H8; try eassumption.
      eapply rqsQ_length_two with (msg1:= rqm) (msg2:= rqdm); try eassumption.
      apply FirstMP_InMP; assumption.

    - disc_rule_conds.
      + elim H14; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
      + elim H13; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
      + destruct rqDown as [rqDown rqdm]; simpl in *.
        assert (rqi_msg rqi <> Some rqdm)
          by (intro Hx; rewrite H45 in Hx; inv Hx; elim H8; auto); clear H8.
        good_locking_get pobj.
        eapply downLockInvORq_down_rqsQ_length_two_False in H8; try eassumption.
        eapply rqsQ_length_two with (msg1:= rqfm) (msg2:= rqdm); try eassumption.
        * intro; subst; auto.
        * apply FirstMP_InMP; assumption.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + disc_rule_conds.
        elim (H9 (idOf rqDown, rmsg0) eq_refl H26).
        left; reflexivity.
      + disc_rule_conds.
        elim (H9 (idOf rqDown, rmsg) eq_refl H26).
        left; reflexivity.

      + assert (exists rin, In rin rins).
        { destruct rins.
          { exfalso.
            red in H31; dest.
            destruct rqTos; [auto|].
            apply eq_sym, map_eq_nil in H37.
            congruence.
          }
          { eexists; left; reflexivity. }
        }
        destruct H15 as [[rsUp rsum] ?].
        assert (In rsUp (idsOf rins))
          by (apply in_map with (f:= idOf) in H15; assumption).
        rewrite H37 in H33.
        eapply RqRsDownMatch_rs_rq in H31; [|eassumption].
        destruct H31 as [cidx [down ?]]; dest.
        rewrite Forall_forall in H10; specialize (H10 _ H15).
        destruct H10 as [oidx [? ?]].
        disc_rule_conds.
        elim H40; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].

      + assert (exists rin, In rin rins).
        { destruct rins.
          { exfalso.
            red in H16; dest.
            destruct rqTos; [auto|].
            apply eq_sym, map_eq_nil in H37.
            congruence.
          }
          { eexists; left; reflexivity. }
        }
        destruct H14 as [[rsUp rsum] ?].
        assert (In rsUp (idsOf rins))
          by (apply in_map with (f:= idOf) in H14; assumption).
        rewrite H37 in H19.
        eapply RqRsDownMatch_rs_rq in H16; [|eassumption].
        destruct H16 as [cidx [down ?]]; dest.
        rewrite Forall_forall in H10; specialize (H10 _ H14).
        destruct H10 as [oidx [? ?]].
        disc_rule_conds.
        elim H36; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].

      + assert (exists rin, In rin rins).
        { destruct rins.
          { exfalso.
            red in H14; dest.
            destruct rqTos; [auto|].
            apply eq_sym, map_eq_nil in H37.
            congruence.
          }
          { eexists; left; reflexivity. }
        }
        destruct H15 as [[rsUp rsum] ?].
        assert (In rsUp (idsOf rins))
          by (apply in_map with (f:= idOf) in H15; assumption).
        rewrite H37 in H16.
        eapply RqRsDownMatch_rs_rq in H14; [|eassumption].
        destruct H14 as [cidx [down ?]]; dest.
        rewrite Forall_forall in H10; specialize (H10 _ H15).
        destruct H10 as [oidx [? ?]].
        disc_rule_conds.
        elim H33; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      elim (H9 (idOf rqDown, rmsg) eq_refl H16).
      left; reflexivity.
  Qed.

  Lemma step_rqDown_no_rsDown_out:
    forall cidx cobj pidx pobj rqDown,
      In cobj sys.(sys_objs) -> cobj.(obj_idx) = cidx ->
      In pobj sys.(sys_objs) -> pobj.(obj_idx) = pidx ->
      parentIdxOf dtr cidx = Some pidx ->
      edgeDownTo dtr cidx = Some (idOf rqDown) ->
      msg_type (valOf rqDown) = MRq ->
      forall st1,
        Reachable (steps step_m) sys st1 ->
        InMPI (st_msgs st1) rqDown ->
        forall oidx ridx rins routs st2,
          step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
          ~ In rqDown rins ->
          forall rsDown,
            idOf rsDown = idOf rqDown ->
            msg_type (valOf rsDown) = MRs ->
            ~ In rsDown routs.
  Proof.
    intros; subst.
    assert (Reachable (steps step_m) sys st2)
      by (eapply reachable_steps;
          [eassumption|apply steps_singleton; eassumption]).
    inv_step; simpl in *.
    intro Hx.
    eapply rqDown_in_rsDown_push_false
      with (cobj0:= cobj) (pobj0:= pobj)
           (dq:= findQ (idOf rqDown) (deqMsgs (idsOf rins) msgs))
      in H0; eauto; try apply Hrrs.
    - destruct H21; red in H8.
      destruct rqDown as [rqDown rqdm]; simpl in *.
      eapply deqMsgs_InMP; eauto.
    - destruct rsDown as [rsDown rsdm]; simpl in *; subst.
      destruct H25.
      rewrite findQ_In_NoDup_enqMsgs with (msg:= rsdm); try assumption.
      reflexivity.
  Qed.

  Lemma atomic_rqDown_no_rsDown_out:
    forall cidx cobj pidx pobj rqDown,
      In cobj sys.(sys_objs) -> cobj.(obj_idx) = cidx ->
      In pobj sys.(sys_objs) -> pobj.(obj_idx) = pidx ->
      parentIdxOf dtr cidx = Some pidx ->
      edgeDownTo dtr cidx = Some (idOf rqDown) ->
      msg_type (valOf rqDown) = MRq ->
      forall inits ins hst outs eouts,
        Atomic inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          InMPI (st_msgs st1) rqDown ->
          steps step_m sys st1 hst st2 ->
          ~ In rqDown inits ->
          forall rsDown,
            idOf rsDown = idOf rqDown ->
            msg_type (valOf rsDown) = MRs ->
            ~ In rsDown outs.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 8; simpl; intros; subst.
    - inv_steps.
      eapply step_rqDown_no_rsDown_out
        with (cobj:= cobj) (pobj:= pobj); eauto.
    - inv_steps.
      intro Hx; apply in_app_or in Hx; destruct Hx.
      + eapply IHAtomic; eauto.
      + assert (Reachable (steps step_m) sys st3) by eauto.
        eapply step_rqDown_no_rsDown_out
          with (cobj:= cobj) (pobj:= pobj) (st1:= st3); eauto.
        * eapply atomic_messages_in_in; eauto.
        * pose proof H9.
          eapply atomic_rqDown_inits_outs_disj with (st1:= st1) in H12; eauto.
          intro Hx; elim H12.
          apply H11 in Hx.
          eapply atomic_eouts_in; eauto.
  Qed.

  Lemma step_rqDown_no_rqDown_out:
    forall cidx pidx pobj rqDown1,
      In pobj sys.(sys_objs) -> pobj.(obj_idx) = pidx ->
      parentIdxOf dtr cidx = Some pidx ->
      edgeDownTo dtr cidx = Some (idOf rqDown1) ->
      msg_type (valOf rqDown1) = MRq ->
      forall st1,
        Reachable (steps step_m) sys st1 ->
        InMPI (st_msgs st1) rqDown1 ->
        forall oidx ridx rins routs st2,
          step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
          ~ In rqDown1 rins ->
          forall rqDown2,
            idOf rqDown2 = idOf rqDown1 ->
            msg_type (valOf rqDown2) = MRq ->
            ~ In rqDown2 routs.
  Proof.
    destruct Hrrs as [? [? [_ ?]]]; intros; subst.
    assert (Reachable (steps step_m) sys st2)
      by (eapply reachable_steps;
          [eassumption|apply steps_singleton; eassumption]).
    pose proof (downLockInv_ok Hiorqs H0 H H1 H3); clear H3.
    inv_step; simpl in *.
    intro Hx.
    good_locking_get pobj.
    eapply downLockInvORq_down_rqsQ_length_two_False in H3; eauto.
    destruct rqDown1 as [down rqdm1]; simpl in *; subst.
    destruct rqDown2 as [down rqdm2]; simpl in *.
    destruct H23, H27; unfold rqsQ.
    rewrite findQ_In_NoDup_enqMsgs with (msg:= rqdm2); auto.
    rewrite filter_app; simpl.
    rewrite H12; simpl.
    rewrite app_length; simpl.
    assert (InMP down rqdm1 (deqMsgs (idsOf rins) msgs)).
    { apply deqMsgs_InMP; eauto. }
    apply rqsQ_length_ge_one in H16; auto.
    unfold rqsQ in H16; lia.
  Qed.

  Lemma atomic_rqDown_no_rqDown_out:
    forall cidx pidx pobj rqDown1,
      In pobj sys.(sys_objs) -> pobj.(obj_idx) = pidx ->
      parentIdxOf dtr cidx = Some pidx ->
      edgeDownTo dtr cidx = Some (idOf rqDown1) ->
      msg_type (valOf rqDown1) = MRq ->
      forall inits ins hst outs eouts,
        Atomic inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          InMPI (st_msgs st1) rqDown1 ->
          steps step_m sys st1 hst st2 ->
          ~ In rqDown1 inits ->
          forall rqDown2,
            idOf rqDown2 = idOf rqDown1 ->
            msg_type (valOf rqDown2) = MRq ->
            ~ In rqDown2 outs.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 6; simpl; intros; subst.
    - inv_steps.
      eapply step_rqDown_no_rqDown_out with (pobj:= pobj); eauto.
    - inv_steps.
      intro Hx; apply in_app_or in Hx; destruct Hx.
      + eapply IHAtomic; eauto.
      + assert (Reachable (steps step_m) sys st3) by eauto.
        eapply step_rqDown_no_rqDown_out with (pobj:= pobj) (st1:= st3); eauto.
        * eapply atomic_messages_in_in; eauto.
        * pose proof H7.
          eapply atomic_rqDown_inits_outs_disj with (st1:= st1) in H11; eauto.
          intro Hx; elim H11.
          apply H9 in Hx.
          eapply atomic_eouts_in; eauto.
  Qed.

  Corollary atomic_rqDown_no_out:
    forall cidx cobj pidx pobj rqDown,
      In cobj sys.(sys_objs) -> cobj.(obj_idx) = cidx ->
      In pobj sys.(sys_objs) -> pobj.(obj_idx) = pidx ->
      parentIdxOf dtr cidx = Some pidx ->
      edgeDownTo dtr cidx = Some (idOf rqDown) ->
      msg_type (valOf rqDown) = MRq ->
      forall inits ins hst outs eouts,
        Atomic inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          InMPI (st_msgs st1) rqDown ->
          steps step_m sys st1 hst st2 ->
          ~ In rqDown inits ->
          forall dmsg,
            idOf dmsg = idOf rqDown ->
            ~ In dmsg outs.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    destruct (msg_type (valOf dmsg)) eqn:Hmt.
    - eapply atomic_rqDown_no_rsDown_out with (cobj:= cobj) (pobj:= pobj); eauto.
    - eapply atomic_rqDown_no_rqDown_out with (pobj:= pobj); eauto.
  Qed.

  Lemma atomic_rqDown_no_rsDown_in:
    forall cidx cobj pidx pobj rqDown,
      In cobj sys.(sys_objs) -> cobj.(obj_idx) = cidx ->
      In pobj sys.(sys_objs) -> pobj.(obj_idx) = pidx ->
      parentIdxOf dtr cidx = Some pidx ->
      edgeDownTo dtr cidx = Some (idOf rqDown) ->
      msg_type (valOf rqDown) = MRq ->
      forall inits ins hst outs eouts,
        Atomic inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          InMPI (st_msgs st1) rqDown ->
          steps step_m sys st1 hst st2 ->
          ~ In rqDown inits ->
          forall rsDown,
            idOf rsDown = idOf rqDown ->
            msg_type (valOf rsDown) = MRs ->
            ~ In rsDown inits ->
            ~ In rsDown ins.
  Proof.
    intros.
    pose proof H6.
    eapply atomic_rqDown_no_rsDown_out
      with (cobj:= cobj) (pobj:= pobj) in H14; eauto.
    apply atomic_messages_ins_outs in H6.
    destruct H6.
    intro Hx; elim H14.
    apply SubList_app_4 in H15.
    apply H15 in Hx.
    apply in_app_or in Hx; destruct Hx; auto.
    exfalso; auto.
  Qed.

  Ltac disc_rule_custom ::=
    try disc_messages_in.

  Lemma step_outside_tree_init_not_inside:
    forall cidx down oidx,
      edgeDownTo dtr cidx = Some down ->
      ~ In oidx (subtreeIndsOf dtr cidx) ->
      forall st1 ridx rins routs st2,
        Reachable (steps step_m) sys st1 ->
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        forall dmsg,
          ~ In (down, dmsg) rins.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    eapply messages_in_cases in H5; eauto.
    destruct H5 as [|[|[|]]]; intro Hx.
    - disc_rule_conds; solve_midx_false.
    - disc_rule_conds.
      elim H3.
      eapply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
      congruence.
    - disc_rule_conds.
      apply in_map with (f:= idOf) in Hx; simpl in Hx.
      rewrite Forall_forall in H6.
      specialize (H6 _ Hx).
      destruct H6 as [rcidx [? ?]].
      solve_midx_false.
    - disc_rule_conds.
      elim H3.
      eapply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
      congruence.
  Qed.

  Lemma atomic_outside_tree_init_not_inside:
    forall cidx down hst,
      edgeDownTo dtr cidx = Some down ->
      DisjList (oindsOf hst) (subtreeIndsOf dtr cidx) ->
      forall inits ins outs eouts,
        Atomic inits ins hst outs eouts ->
        forall s1 s2,
          Reachable (steps step_m) sys s1 ->
          steps step_m sys s1 hst s2 ->
          forall dmsg,
            ~ In (down, dmsg) inits.
  Proof.
    induction 3; simpl; subst; intros.
    - inv_steps.
      simpl in H0.
      specialize (H0 oidx).
      destruct H0; [elim H0; left; reflexivity|].
      eapply step_outside_tree_init_not_inside; eauto.
    - inv_steps.
      eapply IHAtomic; eauto.
      simpl in H0; apply DisjList_cons in H0; dest; assumption.
  Qed.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_RqRsMsgFrom.

  Lemma atomic_NonRqUp_rqDown_separation_ok:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      Forall (NonRqUpL dtr) hst ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cobj pobj rqDown,
          In cobj sys.(sys_objs) ->
          In pobj sys.(sys_objs) ->
          parentIdxOf dtr (obj_idx cobj) = Some (obj_idx pobj) ->
          edgeDownTo dtr (obj_idx cobj) = Some (idOf rqDown) ->
          msg_type (valOf rqDown) = MRq ->
          InMPI s1.(st_msgs) rqDown ->
          ~ In rqDown inits ->
          SubList (oindsOf hst) (subtreeIndsOf dtr (obj_idx cobj)) \/
          DisjList (oindsOf hst) (subtreeIndsOf dtr (obj_idx cobj)).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (atomic_rqDown_no_rsDown_in
                  _ _ _ H6 eq_refl H7 eq_refl H8 H9 H10
                  H2 H4 H11 H5 H12) as Hrqrs.

    generalize dependent s2.
    generalize dependent s1.
    induction H2; simpl; intros; subst.
    - destruct (in_dec idx_dec oidx (subtreeIndsOf dtr (obj_idx cobj))).
      + left; red; intros; dest_in; assumption.
      + right; apply (DisjList_singleton_1 idx_dec); assumption.
    - inv_steps.
      inv H3.
      assert (forall rsDown,
                 idOf rsDown = idOf rqDown ->
                 msg_type (valOf rsDown) = MRs ->
                 ~ In rsDown inits -> ~ In rsDown ins).
      { intros; intro Hx.
        eapply Hrqrs; eauto.
        apply in_or_app; auto.
      }
      specialize (IHAtomic H17 H12 H3); clear H3.
      specialize (IHAtomic _ H15 H16 _ H18).
      destruct IHAtomic.
      + left; apply SubList_cons; [|assumption].
        pose proof (atomic_ext_outs_bounded Hiorqs Hrrs H2 H15 H18 H3).
        eapply SubList_forall in H11; [|eassumption].
        assert (Reachable (steps step_m) sys st2) by eauto.
        eapply step_separation_inside_child_ok; eauto.
        eapply atomic_messages_in_in in H12; try eassumption.
        intro Hx; subst.
        eapply step_rqDown_separation_inside_false; eauto.
      + right; apply (DisjList_cons_inv idx_dec); [assumption|].
        pose proof (atomic_msg_outs_disj Hiorqs Hrrs H2 H15 H18 H3).
        eapply SubList_forall in H11; [|eassumption].
        assert (Reachable (steps step_m) sys st2) by eauto.
        eapply step_separation_outside_ok; eauto.
        pose proof (atomic_messages_in_in H2 H18 _ H16 H12).
        intro Hx; subst.
        eapply step_rqDown_separation_outside_false with (rins:= rins); eauto.
        * clear H13.
          pose proof H2.
          eapply atomic_rqDown_inits_outs_disj in H13; eauto.
          intro Hx; apply H5 in Hx.
          elim H13.
          eapply atomic_eouts_in; eauto.
        * intros; intro Hx.
          eapply Hrqrs; eauto.
          { destruct rsDown as [rsDown rsdm]; simpl in *; subst.
            clear H13.
            eapply atomic_outside_tree_init_not_inside; eauto.
          }
          { apply in_or_app; auto. }
  Qed.

  Lemma atomic_NonRqUp_rqDown_separation_inside:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      Forall (NonRqUpL dtr) hst ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cobj pobj rqDown,
          In cobj sys.(sys_objs) ->
          In pobj sys.(sys_objs) ->
          parentIdxOf dtr (obj_idx cobj) = Some (obj_idx pobj) ->
          edgeDownTo dtr (obj_idx cobj) = Some (idOf rqDown) ->
          msg_type (valOf rqDown) = MRq ->
          InMPI s1.(st_msgs) rqDown ->
          ~ In rqDown inits ->
          forall ioidx,
            In ioidx (oindsOf hst) ->
            In ioidx (subtreeIndsOf dtr (obj_idx cobj)) ->
            SubList (oindsOf hst) (subtreeIndsOf dtr (obj_idx cobj)).
  Proof.
    intros.
    eapply atomic_NonRqUp_rqDown_separation_ok with (cobj:= cobj) in H; eauto.
    destruct H; auto.
    exfalso.
    specialize (H ioidx); destruct H; auto.
  Qed.

  Lemma atomic_NonRqUp_rqDown_separation_outside:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      Forall (NonRqUpL dtr) hst ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cobj pobj rqDown,
          In cobj sys.(sys_objs) ->
          In pobj sys.(sys_objs) ->
          parentIdxOf dtr (obj_idx cobj) = Some (obj_idx pobj) ->
          edgeDownTo dtr (obj_idx cobj) = Some (idOf rqDown) ->
          msg_type (valOf rqDown) = MRq ->
          InMPI s1.(st_msgs) rqDown ->
          ~ In rqDown inits ->
          forall ioidx,
            In ioidx (oindsOf hst) ->
            ~ In ioidx (subtreeIndsOf dtr (obj_idx cobj)) ->
            DisjList (oindsOf hst) (subtreeIndsOf dtr (obj_idx cobj)).
  Proof.
    intros.
    eapply atomic_NonRqUp_rqDown_separation_ok with (cobj:= cobj) in H; eauto.
    destruct H; auto.
    exfalso.
    elim H11; auto.
  Qed.

  (*! Separation by an RsDown message *)

  Lemma step_rsDown_ins_outs_disj:
    forall cidx cobj,
      In cobj sys.(sys_objs) ->
      cobj.(obj_idx) = cidx ->
      forall rsDown pidx,
        parentIdxOf dtr cidx = Some pidx ->
        edgeDownTo dtr cidx = Some (idOf rsDown) ->
        msg_type (valOf rsDown) = MRs ->
        forall st1 oidx ridx rins routs st2,
          Reachable (steps step_m) sys st1 ->
          InMPI (st_msgs st1) rsDown ->
          ~ In rsDown rins ->
          step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
          ~ In rsDown routs.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    assert (Reachable (steps step_m) sys st2).
    { eapply reachable_steps; [eassumption|].
      eapply steps_singleton; eassumption.
    }
    pose proof (upLockInv_ok Hiorqs H0 H H11) as Hlinv; clear H11.
    pose proof (footprints_ok Hiorqs H0 H7) as Hfinv.
    inv_step.
    good_locking_get cobj.
    intro Hx.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      eapply upLockInvORq_down_rssQ_length_two_False; try eassumption.
      solve_q.
      rewrite filter_app; simpl.
      rewrite H12; simpl.
      rewrite app_length; simpl.
      eapply rssQ_length_ge_one in H8; [|assumption].
      unfold rssQ in H8; simpl in H8.
      lia.

    - disc_rule_conds.
      solve_midx_false.

    - disc_rule_conds.
      all: try (rewrite Forall_forall in H38; specialize (H38 _ Hx);
                simpl in H38; rewrite H38 in H6; discriminate).

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + eapply upLockInvORq_down_rssQ_length_two_False; try eassumption.
        solve_q.
        apply parentIdxOf_not_eq in H4; [|apply Hrrs].
        solve_q.
        rewrite filter_app; simpl.
        rewrite H28; simpl.
        rewrite app_length; simpl.
        eapply rssQ_length_ge_one in H8; [|assumption].
        unfold rssQ in H8; simpl in H8.
        lia.
      + eapply upLockInvORq_down_rssQ_length_two_False; try eassumption.
        solve_q.
        rewrite filter_app; simpl.
        rewrite H26; simpl.
        rewrite app_length; simpl.
        eapply rssQ_length_ge_one in H8; [|assumption].
        unfold rssQ in H8; simpl in H8.
        lia.
      + solve_midx_false.

    - disc_rule_conds.
      rewrite Forall_forall in H30; specialize (H30 _ Hx).
      simpl in H30; rewrite H30 in H6; discriminate.
  Qed.

  Lemma atomic_rsDown_inits_outs_disj:
    forall cidx cobj,
      In cobj sys.(sys_objs) ->
      cobj.(obj_idx) = cidx ->
      forall rsDown pidx,
        parentIdxOf dtr cidx = Some pidx ->
        edgeDownTo dtr cidx = Some (idOf rsDown) ->
        msg_type (valOf rsDown) = MRs ->
        forall inits ins hst outs eouts,
          Atomic inits ins hst outs eouts ->
          ~ In rsDown inits ->
          forall st1,
            Reachable (steps step_m) sys st1 ->
            InMPI (st_msgs st1) rsDown ->
            forall st2,
              steps step_m sys st1 hst st2 ->
              ~ In rsDown outs.
  Proof.
    induction 6; simpl; intros; subst.
    - inv_steps.
      eapply step_rsDown_ins_outs_disj; eauto.
    - inv_steps.
      specialize (IHAtomic H10 _ H11 H12 _ H9).
      intro Hx; apply in_app_or in Hx.
      destruct Hx; [auto|].
      assert (Reachable (steps step_m) sys st3) by eauto.
      eapply step_rsDown_ins_outs_disj with (rins:= rins); eauto.
      + eapply atomic_messages_in_in; eauto.
      + intro Hx; apply H6 in Hx.
        elim IHAtomic.
        eapply atomic_eouts_in; eauto.
  Qed.

  Corollary atomic_rsDown_inits_ins_disj:
    forall cidx cobj,
      In cobj sys.(sys_objs) ->
      cobj.(obj_idx) = cidx ->
      forall rsDown pidx,
        parentIdxOf dtr cidx = Some pidx ->
        edgeDownTo dtr cidx = Some (idOf rsDown) ->
        msg_type (valOf rsDown) = MRs ->
        forall inits ins hst outs eouts,
          Atomic inits ins hst outs eouts ->
          ~ In rsDown inits ->
          forall st1,
            Reachable (steps step_m) sys st1 ->
            InMPI (st_msgs st1) rsDown ->
            forall st2,
              steps step_m sys st1 hst st2 ->
              ~ In rsDown ins.
  Proof.
    intros.
    pose proof H4.
    eapply atomic_rsDown_inits_outs_disj in H9; eauto.
    apply atomic_messages_ins_outs in H4.
    destruct H4.
    apply SubList_app_4 in H10.
    intro Hx; apply H10 in Hx.
    apply in_app_or in Hx; destruct Hx; auto.
  Qed.

  Lemma step_rsDown_no_rqDown_in:
    forall cidx cobj pidx pobj rsDown,
      In cobj sys.(sys_objs) -> cobj.(obj_idx) = cidx ->
      In pobj sys.(sys_objs) -> pobj.(obj_idx) = pidx ->
      parentIdxOf dtr cidx = Some pidx ->
      edgeDownTo dtr cidx = Some (idOf rsDown) ->
      msg_type (valOf rsDown) = MRs ->
      forall st1,
        Reachable (steps step_m) sys st1 ->
        InMPI (st_msgs st1) rsDown ->
        forall oidx ridx rins routs st2,
          step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
          forall rqDown,
            idOf rqDown = idOf rsDown ->
            msg_type (valOf rqDown) = MRq ->
            ~ In rqDown rins.
  Proof.
    intros; subst.
    inv_step; simpl in *.
    intro Hx.
    rewrite Forall_forall in H18.
    specialize (H18 _ Hx).
    eapply rsDown_in_rqDown_first_false
      with (cobj0:= cobj) (pobj0:= pobj); eauto; try apply Hrrs.
    simpl; rewrite <-H9; assumption.
  Qed.

  Lemma atomic_rsDown_no_rqDown_in:
    forall cidx cobj pidx pobj rsDown,
      In cobj sys.(sys_objs) -> cobj.(obj_idx) = cidx ->
      In pobj sys.(sys_objs) -> pobj.(obj_idx) = pidx ->
      parentIdxOf dtr cidx = Some pidx ->
      edgeDownTo dtr cidx = Some (idOf rsDown) ->
      msg_type (valOf rsDown) = MRs ->
      forall inits ins hst outs eouts,
        Atomic inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          InMPI (st_msgs st1) rsDown ->
          steps step_m sys st1 hst st2 ->
          ~ In rsDown inits ->
          forall rqDown,
            idOf rqDown = idOf rsDown ->
            msg_type (valOf rqDown) = MRq ->
            ~ In rqDown ins.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 8; simpl; intros; subst.
    - inv_steps.
      eapply step_rsDown_no_rqDown_in
        with (cobj:= cobj) (pobj:= pobj); eauto.
    - inv_steps.
      intro Hx; apply in_app_or in Hx; destruct Hx.
      + eapply IHAtomic; eauto.
      + assert (Reachable (steps step_m) sys st3) by eauto.
        eapply step_rsDown_no_rqDown_in
          with (cobj:= cobj) (pobj:= pobj) (st1:= st3); eauto.
        eapply atomic_messages_in_in; eauto.
  Qed.

  Lemma step_rsDown_no_rsDown_in:
    forall cidx cobj pidx rsDown1,
      In cobj sys.(sys_objs) -> cobj.(obj_idx) = cidx ->
      parentIdxOf dtr cidx = Some pidx ->
      edgeDownTo dtr cidx = Some (idOf rsDown1) ->
      msg_type (valOf rsDown1) = MRs ->
      forall st1,
        Reachable (steps step_m) sys st1 ->
        InMPI (st_msgs st1) rsDown1 ->
        forall oidx ridx rins routs st2,
          step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
          ~ In rsDown1 rins ->
          forall rsDown2,
            idOf rsDown2 = idOf rsDown1 ->
            msg_type (valOf rsDown2) = MRs ->
            ~ In rsDown2 rins.
  Proof.
    destruct Hrrs as [? [? ?]]; intros; subst.
    pose proof (upLockInv_ok Hiorqs H0 H H7).
    inv_step; simpl in *.
    intro Hx.
    good_locking_get cobj.
    eapply upLockInvORq_down_rssQ_length_two_False in H9; eauto.
    destruct rsDown1 as [down rsdm1]; simpl in *; subst.
    destruct rsDown2 as [down rsdm2]; simpl in *.
    destruct H23, H27.

    eapply rssQ_length_two with (msg1:= rsdm1) (msg2:= rsdm2); eauto.
    - intro; subst; auto.
    - rewrite Forall_forall in H22; specialize (H22 _ Hx).
      apply FirstMP_InMP; assumption.
  Qed.

  Lemma atomic_rsDown_no_rsDown_in:
    forall cidx cobj pidx rsDown1,
      In cobj sys.(sys_objs) -> cobj.(obj_idx) = cidx ->
      parentIdxOf dtr cidx = Some pidx ->
      edgeDownTo dtr cidx = Some (idOf rsDown1) ->
      msg_type (valOf rsDown1) = MRs ->
      forall inits ins hst outs eouts,
        Atomic inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          InMPI (st_msgs st1) rsDown1 ->
          steps step_m sys st1 hst st2 ->
          ~ In rsDown1 inits ->
          forall rsDown2,
            idOf rsDown2 = idOf rsDown1 ->
            msg_type (valOf rsDown2) = MRs ->
            ~ In rsDown2 ins.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 6; simpl; intros; subst.
    - inv_steps.
      eapply step_rsDown_no_rsDown_in with (cobj:= cobj); eauto.
    - inv_steps.
      intro Hx; apply in_app_or in Hx; destruct Hx.
      + eapply IHAtomic; eauto.
      + assert (Reachable (steps step_m) sys st3) by eauto.
        eapply step_rsDown_no_rsDown_in with (cobj:= cobj) (st1:= st3); eauto.
        * eapply atomic_messages_in_in; eauto.
        * pose proof H7.
          eapply atomic_rsDown_inits_outs_disj with (st1:= st1) in H11; eauto.
          intro Hx; elim H11.
          apply H9 in Hx.
          eapply atomic_eouts_in; eauto.
  Qed.

  Corollary atomic_rsDown_no_in:
    forall cidx cobj pidx pobj rsDown,
      In cobj sys.(sys_objs) -> cobj.(obj_idx) = cidx ->
      In pobj sys.(sys_objs) -> pobj.(obj_idx) = pidx ->
      parentIdxOf dtr cidx = Some pidx ->
      edgeDownTo dtr cidx = Some (idOf rsDown) ->
      msg_type (valOf rsDown) = MRs ->
      forall inits ins hst outs eouts,
        Atomic inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          InMPI (st_msgs st1) rsDown ->
          steps step_m sys st1 hst st2 ->
          ~ In rsDown inits ->
          forall dmsg,
            idOf dmsg = idOf rsDown ->
            ~ In dmsg ins.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    destruct (msg_type (valOf dmsg)) eqn:Hmt.
    - eapply atomic_rsDown_no_rsDown_in with (cobj:= cobj); eauto.
    - eapply atomic_rsDown_no_rqDown_in with (cobj:= cobj); eauto.
  Qed.

  Lemma step_rsDown_separation_inside_false:
    forall cidx cobj,
      In cobj sys.(sys_objs) ->
      cobj.(obj_idx) = cidx ->
      forall rsDown pidx,
        parentIdxOf dtr cidx = Some pidx ->
        edgeDownTo dtr cidx = Some (idOf rsDown) ->
        msg_type (valOf rsDown) = MRs ->
        forall st1,
          Reachable (steps step_m) sys st1 ->
          InMPI (st_msgs st1) rsDown ->
          forall rins (Hrins: rins <> nil),
            Forall (fun rin =>
                      exists oidx,
                        RqRsMsgFrom dtr oidx rin /\
                        In oidx (subtreeIndsOf dtr cidx)) rins ->
            forall ridx routs st2,
              step_m sys st1 (RlblInt pidx ridx rins routs) st2 ->
              False.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok Hiorqs H0 H7) as Hftinv.
    pose proof (upLockInv_ok Hiorqs H0 H H7) as Hulinv.
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      destruct (idx_dec cidx (obj_idx cobj)); subst.
      + disc_rule_conds.
        good_locking_get cobj.
        eapply upLockInvORq_rqUp_down_rssQ_False in H3; try eassumption.
        * eapply findQ_length_ge_one.
          apply FirstMP_InMP; eassumption.
        * eapply rssQ_length_ge_one; [|eassumption].
          assumption.
      + eapply subtreeIndsOf_child_disj in n; try eassumption; [|apply Hrrs].
        specialize (n cidx); destruct n; auto.
        elim H3; eapply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
        congruence.

    - disc_rule_conds.
      pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H28).
      destruct H10 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      eapply parent_parent_in_False with (oidx2:= obj_idx obj);
        try apply Hrrs; eassumption.

    - disc_rule_conds.
      + destruct (idx_dec cidx (obj_idx cobj)); subst.
        * disc_rule_conds.
          good_locking_get cobj.
          eapply upLockInvORq_rqUp_down_rssQ_False in H3; try eassumption.
          { eapply findQ_length_ge_one.
            apply FirstMP_InMP; eassumption.
          }
          { eapply rssQ_length_ge_one; [|eassumption].
            assumption.
          }
        * eapply subtreeIndsOf_child_disj in n; try eassumption; [|apply Hrrs].
          specialize (n cidx); destruct n; auto.
          elim H9; eapply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
          congruence.
      + destruct (idx_dec (obj_idx upCObj) (obj_idx cobj)); subst.
        * rewrite e in *.
          disc_rule_conds.
          good_locking_get cobj.
          eapply upLockInvORq_rqUp_down_rssQ_False in H9; try eassumption.
          { eapply findQ_length_ge_one.
            apply FirstMP_InMP; eassumption.
          }
          { eapply rssQ_length_ge_one; [|eassumption].
            assumption.
          }
        * eapply subtreeIndsOf_child_disj in n; try eassumption; [|apply Hrrs].
          specialize (n (obj_idx upCObj)); destruct n; auto.
          elim H9; eapply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
          congruence.
      + pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H3).
        destruct H14 as [rqUp [rsUp [pidx ?]]]; dest.
        disc_rule_conds.
        eapply parent_parent_in_False with (oidx2:= obj_idx obj);
          try apply Hrrs; eassumption.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H12).
        destruct H31 as [rqUp [rsUp [pidx ?]]]; dest.
        disc_rule_conds.
        eapply parent_parent_in_False with (oidx1:= obj_idx cobj) (oidx2:= obj_idx obj);
          try apply Hrrs; eassumption.
      + pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H12).
        destruct H26 as [rqUp [rsUp [pidx ?]]]; dest.
        disc_rule_conds.
        eapply parent_parent_in_False with (oidx1:= obj_idx cobj) (oidx2:= obj_idx obj);
          try apply Hrrs; eassumption.

      + (* Not possible for RsDown and RsUp to be together *)
        assert (exists rsUp rsum,
                   In (rsUp, rsum) rins /\
                   rsEdgeUpFrom dtr (obj_idx cobj) = Some rsUp /\
                   InMP rsUp rsum msgs).
        { destruct rins as [|[rsUp rsum] ?].
          { apply eq_sym, map_eq_nil in H34.
            destruct rqTos; [exfalso; auto|congruence].
          }
          { inv H9; destruct H32 as [oidx [? ?]].
            eapply RqRsDownMatch_rs_rq in H28; [|rewrite <-H34; left; reflexivity].
            destruct H28 as [cidx [down ?]]; dest; simpl in *.
            disc_rule_conds.
            eapply inside_child_outside_parent_case in H30;
              try apply Hrrs; eauto;
                [|apply parent_not_in_subtree; [apply Hrrs|]; assumption].
            subst; exists rsUp, rsum.
            repeat split; auto.
            apply FirstMP_InMP; assumption.
          }
        }
        destruct H12 as [rsUp [rsum ?]]; dest.
        eapply rsDown_in_rsUp_in_false
          with (cobj0:= cobj) (pobj:= obj)
               (down:= idOf rsDown) (rsdm:= valOf rsDown)
               (rsUp0:= rsUp) (rsum0:= rsum); eauto; try apply Hrrs.

      + (* Not possible for RsDown and RsUp to be together *)
        assert (exists rsUp rsum,
                   In (rsUp, rsum) rins /\
                   rsEdgeUpFrom dtr (obj_idx cobj) = Some rsUp /\
                   InMP rsUp rsum msgs).
        { destruct rins as [|[rsUp rsum] ?].
          { apply eq_sym, map_eq_nil in H34.
            destruct rqTos; [exfalso; auto|congruence].
          }
          { inv H9; destruct H28 as [oidx [? ?]].
            eapply RqRsDownMatch_rs_rq in H13; [|rewrite <-H34; left; reflexivity].
            destruct H13 as [cidx [down ?]]; dest; simpl in *.
            disc_rule_conds.
            eapply inside_child_outside_parent_case in H26;
              try apply Hrrs; eauto;
                [|apply parent_not_in_subtree; [apply Hrrs|]; assumption].
            subst; exists rsUp, rsum.
            repeat split; auto.
            apply FirstMP_InMP; assumption.
          }
        }
        destruct H14 as [rsUp [rsum ?]]; dest.
        eapply rsDown_in_rsUp_in_false
          with (cobj0:= cobj) (pobj:= obj)
               (down:= idOf rsDown) (rsdm:= valOf rsDown)
               (rsUp0:= rsUp) (rsum0:= rsum); eauto; try apply Hrrs.

      + (* Not possible for RsDown and RsUp to be together *)
        assert (exists rsUp rsum,
                   In (rsUp, rsum) rins /\
                   rsEdgeUpFrom dtr (obj_idx cobj) = Some rsUp /\
                   InMP rsUp rsum msgs).
        { destruct rins as [|[rsUp rsum] ?].
          { apply eq_sym, map_eq_nil in H34.
            destruct rqTos; [exfalso; auto|congruence].
          }
          { inv H9; destruct H14 as [oidx [? ?]].
            eapply RqRsDownMatch_rs_rq in H11; [|rewrite <-H34; left; reflexivity].
            destruct H11 as [cidx [down ?]]; dest; simpl in *.
            disc_rule_conds.
            eapply inside_child_outside_parent_case in H13;
              try apply Hrrs; eauto;
                [|apply parent_not_in_subtree; [apply Hrrs|]; assumption].
            subst; exists rsUp, rsum.
            repeat split; auto.
            apply FirstMP_InMP; assumption.
          }
        }
        destruct H12 as [rsUp [rsum ?]]; dest.
        eapply rsDown_in_rsUp_in_false
          with (cobj0:= cobj) (pobj:= obj)
               (down:= idOf rsDown) (rsdm:= valOf rsDown)
               (rsUp0:= rsUp) (rsum0:= rsum); eauto; try apply Hrrs.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H10).
      destruct H29 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      eapply parent_parent_in_False
        with (oidx1:= obj_idx cobj) (oidx2:= obj_idx obj);
        try apply Hrrs; eassumption.
  Qed.

  Lemma step_rsDown_separation_outside_false:
    forall cidx pobj rsDown,
      In pobj sys.(sys_objs) ->
      parentIdxOf dtr cidx = Some (obj_idx pobj) ->
      edgeDownTo dtr cidx = Some (idOf rsDown) ->
      msg_type (valOf rsDown) = MRs ->
      forall st1,
        Reachable (steps step_m) sys st1 ->
        InMPI (st_msgs st1) rsDown ->
        forall rins,
          rins <> nil ->
          ~ In rsDown rins ->
          Forall (fun rin =>
                    exists oidx,
                      RqRsMsgFrom dtr oidx rin /\
                      ~ In oidx (subtreeIndsOf dtr cidx)) rins ->
          forall ridx routs st2,
            step_m sys st1 (RlblInt cidx ridx rins routs) st2 ->
            False.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok Hiorqs H0 H6) as Hftinv.
    pose proof (upLockInv_ok Hiorqs H0 H H6) as Hulinv.
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      good_locking_get obj.
      eapply upLockInvORq_down_rssQ_length_one_locked in H10;
        try eassumption;
        [|apply rssQ_length_ge_one with (msg:= valOf rsDown); auto].
      dest; disc_rule_conds; auto.

    - disc_rule_conds.
      eapply rsDown_in_rqDown_first_false
        with (cobj:= obj) (pobj0:= pobj) (rsdm:= valOf rsDown);
        eauto; try apply Hrrs.

    - disc_rule_conds.
      + elim H13; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
      + elim H12; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
      + eapply rsDown_in_rqDown_first_false
          with (cobj:= obj) (pobj0:= pobj) (rsdm:= valOf rsDown);
          eauto; try apply Hrrs.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + destruct rsDown as [rsDown rsdm]; simpl in *.
        disc_rule_conds.
        assert (rmsg0 <> rsdm) by (intro Hx; subst; elim H9; auto); clear H9.
        good_locking_get obj.
        eapply upLockInvORq_down_rssQ_length_two_False in H9; try eassumption.
        eapply rssQ_length_two with (msg1:= rmsg0) (msg2:= rsdm); try eassumption.
        apply FirstMP_InMP; assumption.
      + destruct rsDown as [rsDown rsdm]; simpl in *.
        disc_rule_conds.
        assert (rmsg <> rsdm) by (intro Hx; subst; elim H6; auto); clear H6.
        good_locking_get obj.
        eapply upLockInvORq_down_rssQ_length_two_False in H6; try eassumption.
        eapply rssQ_length_two with (msg1:= rmsg) (msg2:= rsdm); try eassumption.
        apply FirstMP_InMP; assumption.

      + assert (exists rin, In rin rins).
        { destruct rins.
          { exfalso.
            destruct rqTos; [auto|].
            apply eq_sym, map_eq_nil in H36.
            congruence.
          }
          { eexists; left; reflexivity. }
        }
        destruct H14 as [[rsUp rsum] ?].
        assert (In rsUp (idsOf rins))
          by (apply in_map with (f:= idOf) in H14; assumption).
        rewrite H36 in H32.
        eapply RqRsDownMatch_rs_rq in H30; [|eassumption].
        destruct H30 as [cidx [down ?]]; dest.
        rewrite Forall_forall in H10; specialize (H10 _ H14).
        destruct H10 as [oidx [? ?]].
        disc_rule_conds.
        elim H39; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].

      + assert (exists rin, In rin rins).
        { destruct rins.
          { exfalso.
            destruct rqTos; [auto|].
            apply eq_sym, map_eq_nil in H36.
            congruence.
          }
          { eexists; left; reflexivity. }
        }
        destruct H13 as [[rsUp rsum] ?].
        assert (In rsUp (idsOf rins))
          by (apply in_map with (f:= idOf) in H13; assumption).
        rewrite H36 in H18.
        eapply RqRsDownMatch_rs_rq in H15; [|eassumption].
        destruct H15 as [cidx [down ?]]; dest.
        rewrite Forall_forall in H10; specialize (H10 _ H13).
        destruct H10 as [oidx [? ?]].
        disc_rule_conds.
        elim H35; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].

      + assert (exists rin, In rin rins).
        { destruct rins.
          { exfalso.
            destruct rqTos; [auto|].
            apply eq_sym, map_eq_nil in H36.
            congruence.
          }
          { eexists; left; reflexivity. }
        }
        destruct H14 as [[rsUp rsum] ?].
        assert (In rsUp (idsOf rins))
          by (apply in_map with (f:= idOf) in H14; assumption).
        rewrite H36 in H15.
        eapply RqRsDownMatch_rs_rq in H13; [|eassumption].
        destruct H13 as [cidx [down ?]]; dest.
        rewrite Forall_forall in H10; specialize (H10 _ H14).
        destruct H10 as [oidx [? ?]].
        disc_rule_conds.
        elim H32; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      destruct rsDown as [rsDown rsdm]; simpl in *.
      pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H4).
      destruct H14 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      assert (rmsg <> rsdm) by (intro Hx; subst; elim H9; auto); clear H9.
      good_locking_get obj.
      eapply upLockInvORq_down_rssQ_length_two_False in H9; try eassumption.
      eapply rssQ_length_two with (msg1:= rmsg) (msg2:= rsdm); try eassumption.
      apply FirstMP_InMP; assumption.
  Qed.

  Lemma atomic_rsDown_separation_ok:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cobj pobj rsDown,
          In cobj sys.(sys_objs) ->
          In pobj sys.(sys_objs) ->
          parentIdxOf dtr (obj_idx cobj) = Some (obj_idx pobj) ->
          edgeDownTo dtr (obj_idx cobj) = Some (idOf rsDown) ->
          msg_type (valOf rsDown) = MRs ->
          InMPI s1.(st_msgs) rsDown ->
          ~ In rsDown inits ->
          SubList (oindsOf hst) (subtreeIndsOf dtr (obj_idx cobj)) \/
          DisjList (oindsOf hst) (subtreeIndsOf dtr (obj_idx cobj)).
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst.
    - destruct (in_dec idx_dec oidx (subtreeIndsOf dtr (obj_idx cobj))).
      + left; red; intros; dest_in; assumption.
      + right; apply (DisjList_singleton_1 idx_dec); assumption.
    - inv_steps.
      specialize (IHAtomic _ _ H8 H17 _ _ _ H10 H11 H12 H13 H14 H15 H16).
      destruct IHAtomic.
      + left; apply SubList_cons; [|assumption].
        pose proof (atomic_ext_outs_bounded Hiorqs Hrrs H2 H8 H17 H5).
        eapply SubList_forall in H6; [|eassumption].
        assert (Reachable (steps step_m) sys st2) by eauto.
        eapply step_separation_inside_child_ok; eauto.
        eapply atomic_messages_in_in in H17; try eassumption.
        intro Hx; subst.
        eapply step_rsDown_separation_inside_false with (cobj:= cobj); eauto.
      + right; apply (DisjList_cons_inv idx_dec); [assumption|].
        pose proof (atomic_msg_outs_disj Hiorqs Hrrs H2 H8 H17 H5).
        eapply SubList_forall in H6; [|eassumption].
        assert (Reachable (steps step_m) sys st2) by eauto.
        eapply step_separation_outside_ok; eauto.
        pose proof (atomic_messages_in_in H2 H17 _ H15 H16).
        intro Hx; subst.
        eapply step_rsDown_separation_outside_false with (rins:= rins); eauto.
        clear H7; pose proof H2.
        eapply atomic_rsDown_inits_outs_disj with (cobj:= cobj) in H7; eauto.
        intro Hx; eapply H4 in Hx.
        elim H7; eapply atomic_eouts_in; eauto.
  Qed.

  Corollary atomic_rsDown_separation_inside:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cobj pobj rsDown,
          In cobj sys.(sys_objs) ->
          In pobj sys.(sys_objs) ->
          parentIdxOf dtr (obj_idx cobj) = Some (obj_idx pobj) ->
          edgeDownTo dtr (obj_idx cobj) = Some (idOf rsDown) ->
          msg_type (valOf rsDown) = MRs ->
          InMPI s1.(st_msgs) rsDown ->
          ~ In rsDown inits ->
          forall ioidx,
            In ioidx (oindsOf hst) ->
            In ioidx (subtreeIndsOf dtr (obj_idx cobj)) ->
            SubList (oindsOf hst) (subtreeIndsOf dtr (obj_idx cobj)).
  Proof.
    intros.
    eapply atomic_rsDown_separation_ok with (cobj:= cobj) in H; eauto.
    destruct H; auto.
    exfalso.
    specialize (H ioidx); destruct H; auto.
  Qed.

  Corollary atomic_rsDown_separation_outside:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall cobj pobj rsDown,
          In cobj sys.(sys_objs) ->
          In pobj sys.(sys_objs) ->
          parentIdxOf dtr (obj_idx cobj) = Some (obj_idx pobj) ->
          edgeDownTo dtr (obj_idx cobj) = Some (idOf rsDown) ->
          msg_type (valOf rsDown) = MRs ->
          InMPI s1.(st_msgs) rsDown ->
          ~ In rsDown inits ->
          forall ioidx,
            In ioidx (oindsOf hst) ->
            ~ In ioidx (subtreeIndsOf dtr (obj_idx cobj)) ->
            DisjList (oindsOf hst) (subtreeIndsOf dtr (obj_idx cobj)).
  Proof.
    intros.
    eapply atomic_rsDown_separation_ok with (cobj:= cobj) in H; eauto.
    destruct H; auto.
    exfalso.
    elim H10; auto.
  Qed.

End Separation.

Close Scope list.
Close Scope fmap.
