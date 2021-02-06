Require Import PeanoNat Lia List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvMsg.

Require Export RqRsInvUpLock RqRsInvDownLock.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Ltac good_locking_get obj :=
  try match goal with
      | [Hlock: UpLockInv _ ?sys _, Ho: In obj (sys_objs ?sys) |- _] =>
        let H := fresh "H" in
        pose proof Hlock as H;
        specialize (H (obj_idx obj)); simpl in H;
        specialize (H (in_map obj_idx _ _ Ho)); dest
      end;
  try match goal with
      | [Hlock: DownLockInv _ ?sys _, Ho: In obj (sys_objs ?sys) |- _] =>
        let H := fresh "H" in
        pose proof Hlock as H;
        specialize (H (obj_idx obj)); simpl in H;
        specialize (H (in_map obj_idx _ _ Ho)); dest
      end.

Ltac disc_lock_conds :=
  match goal with
  | [H: OLockedTo _ _ _ |- _] => red in H
  | [H: UpLockInvORq _ _ _ _ _ |- _] => red in H; mred; simpl in H; mred
  | [H: UpLockRsFromParent _ _ _ /\ UpLockedInv _ _ _ _ |- _] => destruct H
  | [H: UpLockedInv _ _ _ _ |- _] =>
    let rqUp := fresh "rqUp" in
    let down := fresh "down" in
    let pidx := fresh "pidx" in
    destruct H as [rqUp [down [pidx ?]]]; dest
  | [H: DownLockInvORq _ _ _ _ _ |- _] => red in H; mred; simpl in H; mred
  | [H: DownLockRssToParent _ _ _ /\ DownLockedInv _ _ _ _ _ |- _] => destruct H
  end.

Section RqRsDown.
  Context `{dv: DecValue} `{oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System).
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hrr: GoodRqRsSys dtr sys)
             (Hsd: RqRsDTree dtr sys)
             (Hers: GoodExtRssSys sys).

  Definition ONoDownLock (orqs: ORqs Msg) (oidx: IdxT) :=
    orqs@[oidx] >>=[True] (fun orq => orq@[downRq] = None).

  Definition ODownRq (orqs: ORqs Msg) (msgs: MessagePool Msg) (oidx: IdxT) (down: IdxT) :=
    orqs@[oidx] >>=[False]
        (fun orq =>
           orq@[downRq] >>=[False]
              (fun rqid =>
                 forall cidx rsUp,
                   edgeDownTo dtr cidx = Some down ->
                   rsEdgeUpFrom dtr cidx = Some rsUp ->
                   In rsUp (map fst rqid.(rqi_rss)) ->
                   rqsQ msgs down <> nil)).

  Definition NoRqRsDown (st: State) :=
    forall cobj pobj,
      In cobj sys.(sys_objs) ->
      In pobj sys.(sys_objs) ->
      parentIdxOf dtr (obj_idx cobj) = Some (obj_idx pobj) ->
      forall down,
        edgeDownTo dtr (obj_idx cobj) = Some down ->
        forall rsdm,
          rsdm.(msg_type) = MRs ->
          InMP down rsdm st.(st_msgs) ->
          ONoDownLock st.(st_orqs) (obj_idx pobj) \/
          (ODownRq st.(st_orqs) st.(st_msgs) (obj_idx pobj) down /\
           FirstMP st.(st_msgs) down rsdm).

  Lemma noRqRsDown_InvInit:
    InvInit sys NoRqRsDown.
  Proof.
    do 2 red; intros.
    simpl in *.
    inv H4.
  Qed.

  Ltac disc_NoRqRsDown :=
    match goal with
    | [H: NoRqRsDown _ |- NoRqRsDown _] =>
      let cobj := fresh "cobj" in
      let pobj := fresh "pobj" in
      let H0 := fresh in
      let H1 := fresh in
      let H2 := fresh in
      let down := fresh "down" in
      let H3 := fresh in
      let rsdm := fresh "rsdm" in
      let H4 := fresh in
      red; intros cobj pobj H0 H1 H2 down H3 rsdm H4 ?;
      specialize (H _ _ H0 H1 H2 _ H3 _ H4); simpl in *
    end.

  Lemma noRqRsDown_step_ext_in:
    forall oss orqs msgs eins,
      NoRqRsDown {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      eins <> nil ->
      ValidMsgsExtIn sys eins ->
      NoRqRsDown {| st_oss := oss;
                    st_orqs := orqs;
                    st_msgs := enqMsgs eins msgs |}.
  Proof.
    intros; disc_NoRqRsDown.
    assert (~ In down (idsOf eins)).
    { destruct H1.
      apply DisjList_In_1 with (l2:= sys_minds sys).
      { eapply DisjList_SubList; eauto.
        apply DisjList_comm.
        apply sys_minds_sys_merqs_DisjList.
      }
      { eapply rqrsDTree_edgeDownTo_sys_minds; [apply Hsd|..]; eauto.
        apply in_map; assumption.
      }
    }

    apply InMP_enqMsgs_or in H7; destruct H7.
    - exfalso.
      apply in_map with (f:= idOf) in H7; simpl in H7; auto.
    - specialize (H H7).
      destruct H; [left; assumption|].
      dest; right; split.
      + red in H; red.
        destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
        destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
        intros; specialize (H _ _ H10 H11 H12).
        solve_q.
        rewrite findQ_not_In_enqMsgs by assumption.
        assumption.
      + apply FirstMP_enqMsgs; assumption.
  Qed.

  Lemma noRqRsDown_step_ext_out:
    forall oss orqs msgs eouts,
      NoRqRsDown {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      eouts <> nil ->
      Forall (FirstMPI msgs) eouts ->
      ValidMsgsExtOut sys eouts ->
      NoRqRsDown {| st_oss := oss;
                    st_orqs := orqs;
                    st_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    intros; disc_NoRqRsDown.
    apply InMP_deqMsgs in H8.
    specialize (H H8).
    destruct H; [left; assumption|].
    assert (~ In down (idsOf eouts)).
    { destruct H2.
      apply DisjList_In_1 with (l2:= sys_minds sys).
      { eapply DisjList_SubList; eauto.
        apply DisjList_comm.
        apply sys_minds_sys_merss_DisjList.
      }
      { eapply rqrsDTree_edgeDownTo_sys_minds; [apply Hsd|..]; eauto.
        apply in_map; assumption.
      }
    }

    dest; right; split.
    - red in H; red.
      destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
      destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
      intros; specialize (H _ _ H11 H12 H13).
      solve_q.
      rewrite findQ_not_In_deqMsgs by assumption.
      assumption.
    - apply FirstMP_deqMsgs; assumption.
  Qed.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_NoRqRsDown.

  Lemma rsDown_rqsQ_nil_in_first:
    forall st,
      Reachable (steps step_m) sys st ->
      forall cobj,
        In cobj sys.(sys_objs) ->
        forall msgs down rsdm,
          st.(st_msgs) = msgs ->
          edgeDownTo dtr (obj_idx cobj) = Some down ->
          rsdm.(msg_type) = MRs ->
          InMP down rsdm msgs ->
          rqsQ msgs down = nil ->
          FirstMP msgs down rsdm.
  Proof.
    intros; subst.
    pose proof (upLockInv_ok Hiorqs Hrr Hsd H).
    good_locking_get cobj.
    pose proof (edgeDownTo_Some (proj1 (proj2 Hsd)) _ H2).
    destruct H7 as [rqUp [rsUp [pidx ?]]]; dest.
    eapply upLockInvORq_down_rssQ_length_one_locked in H6; eauto;
      [|eapply rssQ_length_ge_one; eauto].
    destruct H6 as [rrqUp [rdown [rpidx ?]]]; dest.
    repeat disc_rule_minds.
    apply InMP_FirstMP; [assumption|].
    rewrite rqsQ_rssQ_length.
    rewrite H5; simpl.
    assumption.
  Qed.

  Lemma rsDown_in_deqMP_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall cobj,
        In cobj sys.(sys_objs) ->
        forall msgs down rsdm1 rsdm2,
          st.(st_msgs) = msgs ->
          edgeDownTo dtr (obj_idx cobj) = Some down ->
          rsdm1.(msg_type) = MRs ->
          FirstMP msgs down rsdm1 ->
          rsdm2.(msg_type) = MRs ->
          InMP down rsdm2 (deqMP down msgs) ->
          False.
  Proof.
    intros; subst.
    pose proof (upLockInv_ok Hiorqs Hrr Hsd H).
    good_locking_get cobj.
    pose proof (edgeDownTo_Some (proj1 (proj2 Hsd)) _ H2).
    destruct H8 as [rqUp [rsUp [pidx ?]]]; dest.
    eapply upLockInvORq_down_rssQ_length_one_locked in H7; eauto.
    - dest; red in H11.
      destruct H11 as [rrqUp [rdown [rpidx ?]]]; dest.
      repeat disc_rule_minds.

      clear -H3 H4 H5 H6 H15.
      unfold InMP, FirstMP, firstMP, rssQ, deqMP in *.
      destruct (findQ rdown (st_msgs st)); [discriminate|].
      simpl in H4; inv H4.
      simpl in H15; rewrite H3 in H15; simpl in H15.
      unfold findQ in H6; mred; simpl in H6.
      destruct (filter (fun msg => msg_type msg) q) eqn:Hq.
      + assert (In rsdm2 (filter (fun msg => msg_type msg) q)).
        { apply filter_In.
          split; auto.
        }
        rewrite Hq in H; elim H.
      + simpl in H15; lia.
    - eapply rssQ_length_ge_one; eauto.
      eapply InMP_deqMP; eassumption.
  Qed.

  Lemma rsUp_in_deqMP_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall pobj,
        In pobj sys.(sys_objs) ->
        forall cidx msgs rsUp rsum1 rsum2,
          st.(st_msgs) = msgs ->
          parentIdxOf dtr cidx = Some (obj_idx pobj) ->
          rsEdgeUpFrom dtr cidx = Some rsUp ->
          FirstMP msgs rsUp rsum1 ->
          InMP rsUp rsum2 (deqMP rsUp msgs) ->
          False.
  Proof.
    intros; subst.
    pose proof (downLockInv_ok Hiorqs Hrr Hsd Hers H).
    good_locking_get pobj.
    eapply downLockInvORq_rsUp_length_two_False in H6; eauto.

    clear -H4 H5.
    unfold InMP, FirstMP, firstMP, deqMP in *.
    destruct (findQ rsUp (st_msgs st)); [discriminate|].
    simpl in H4; inv H4.
    unfold findQ in H5; mred; simpl in H5.
    destruct q; [elim H5|].
    simpl; lia.
  Qed.

  Lemma noRqRsDown_step_int:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      NoRqRsDown st1 ->
      forall oidx ridx rins routs st2,
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        NoRqRsDown st2.
  Proof.
    intros.
    pose proof (footprints_ok Hiorqs Hrr H) as Hftinv.
    assert (Reachable (steps step_m) sys st2) as Hnrch
      by (eapply reachable_steps; [eassumption|apply steps_singleton; eassumption]).
    pose proof (upLockInv_ok Hiorqs Hrr Hsd Hnrch) as Hulinv.
    pose proof (downLockInv_ok Hiorqs Hrr Hsd Hers H) as Hdlinv.
    clear Hnrch.

    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      + replace (orqs +[obj_idx obj <- norq]) with orqs by meq.
        apply H0; assumption.
      + destruct (idx_dec (obj_idx obj) (obj_idx pobj)).
        * eapply obj_same_id_in_system_same in e; eauto; subst.
          left; red; mred.
        * apply InMP_enqMP_or in H8; destruct H8;
            [exfalso; dest; subst; disc_rule_conds; auto|].
          apply InMP_deqMP in H8.
          specialize (H0 H8); destruct H0.
          { left; red; mred. }
          { dest; right; split.
            { red in H0; red; mred.
              destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
              destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
              intros; specialize (H0 _ _ H17 H20 H24).
              assert (cidx <> cidx0) by (intro Hx; subst; disc_rule_conds; auto).
              solve_q; assumption.
            }
            { apply FirstMP_enqMP.
              apply FirstMP_deqMP; [|assumption].
              solve_midx_neq.
            }
          }

    - disc_rule_conds.
      destruct (idx_dec (obj_idx obj) (obj_idx pobj)).
      + eapply obj_same_id_in_system_same in e; eauto; subst.
        left; red; mred.
      + apply InMP_enqMP_or in H15; destruct H15;
          [exfalso; dest; subst; solve_midx_false|].
        apply InMP_deqMP in H11; specialize (H0 H11).
        destruct (idx_dec (obj_idx cobj) (obj_idx obj)).
        * exfalso.
          eapply obj_same_id_in_system_same in e; eauto; subst.
          disc_rule_conds.
          destruct H0.
          { good_locking_get pobj.
            eapply downLockInvORq_down_rqsQ_length_one_locked in H3; eauto;
              [|eapply rqsQ_length_ge_one; eauto;
                apply FirstMP_InMP; auto].
            destruct H3 as [rqid ?]; dest.
            red in H0.
            destruct (orqs@[obj_idx pobj]) as [orq|]; simpl in *; [|discriminate].
            congruence.
          }
          { dest; pose proof (FirstMP_eq H4 H21).
            subst; simpl in *.
            rewrite H5 in H24; discriminate.
          }
        * destruct H0; [left; red; mred|].
          dest; right; split.
          { red in H0; red; mred.
            destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
            destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
            intros; specialize (H0 _ _ H17 H19 H23).
            solve_q; assumption.
          }
          { apply FirstMP_enqMP.
            apply FirstMP_deqMP; [|assumption].
            solve_midx_neq.
          }

    - disc_rule_conds.
      + apply InMP_enqMP_or in H24; destruct H24;
          [exfalso; dest; subst; disc_rule_conds; auto|].
        specialize (H0 H11).
        destruct (idx_dec (obj_idx obj) (obj_idx pobj)).
        * eapply obj_same_id_in_system_same in e; eauto; subst.
          destruct H0.
          { left; red in H0; red; repeat (simpl; mred). }
          { dest; right; split.
            { red in H0; red; repeat (simpl; mred).
              destruct (porq@[downRq]) eqn:Hrqid; simpl in *; auto.
              intros; specialize (H0 _ _ H23 H24 H26).
              solve_q; assumption.
            }
            { apply FirstMP_enqMP; assumption. }
          }
        * destruct H0.
          { left; red in H0; red; mred. }
          { dest; right; split.
            { red in H0; red; mred.
              destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
              destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
              intros; specialize (H0 _ _ H23 H24 H26).
              solve_q; assumption.
            }
            { apply FirstMP_enqMP; assumption. }
          }

      + apply InMP_enqMP_or in H28; destruct H28;
          [exfalso; dest; subst; disc_rule_conds; auto|].
        apply InMP_deqMP in H11.
        specialize (H0 H11).
        destruct (idx_dec (obj_idx obj) (obj_idx pobj)).
        * eapply obj_same_id_in_system_same in e; eauto; subst.
          destruct H0.
          { left; red in H0; red; repeat (simpl; mred). }
          { dest; right; split.
            { red in H0; red; repeat (simpl; mred).
              destruct (porq@[downRq]) eqn:Hrqid; simpl in *; auto.
              intros; specialize (H0 _ _ H23 H28 H31).
              solve_q; assumption.
            }
            { apply FirstMP_enqMP.
              apply FirstMP_deqMP; [|assumption].
              solve_midx_neq.
            }
          }
        * destruct H0.
          { left; red in H0; red; mred. }
          { dest; right; split.
            { red in H0; red; mred.
              destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
              destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
              intros; specialize (H0 _ _ H23 H28 H31).
              solve_q; assumption.
            }
            { apply FirstMP_enqMP.
              apply FirstMP_deqMP; [|assumption].
              solve_midx_neq.
            }
          }

      + apply InMP_enqMsgs_or in H17; destruct H17.
        1:{ exfalso.
            rewrite Forall_forall in H29; specialize (H29 _ H11).
            simpl in H29; rewrite H8 in H29; discriminate.
        }
        specialize (H0 H11).
        destruct (idx_dec (obj_idx obj) (obj_idx pobj)).
        * eapply obj_same_id_in_system_same in e; eauto; subst.
          destruct H0; [|dest; exfalso; red in H0; mred].
          right; split.
          { destruct (in_dec idx_dec down (idsOf routs)).
            { red; repeat (simpl; mred).
              intros; solve_q.
              destruct H16.
              apply in_map_iff in i; destruct i as [[down' rqdm] ?]; dest.
              simpl in *; subst.
              erewrite findQ_In_NoDup_enqMsgs; try eassumption.
              rewrite Forall_forall in H29; specialize (H29 _ H24); simpl in H29.
              rewrite filter_app; simpl.
              rewrite H29; simpl.
              destruct (filter _ _); discriminate.
            }
            { red; repeat (simpl; mred).
              intros; disc_rule_conds.
              elim n; clear n.
              eapply RqRsDownMatch_rs_rq in H33; [|eassumption].
              destruct H33 as [cidx [rdown ?]]; dest.
              disc_rule_conds.
            }
          }
          { apply FirstMP_enqMsgs.
            eapply rsDown_rqsQ_nil_in_first with (cobj:= cobj); eauto.
            good_locking_get pobj.
            red in H20; mred.
            specialize (H20 _ H3).
            destruct H20 as [rdown [rsUp ?]]; dest.
            disc_rule_conds.
            apply H22.
          }
        * destruct H0; [left; red; mred|].
          dest; right; split.
          { red in H0; red; mred.
            destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
            destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
            intros; specialize (H0 _ _ H20 H21 H22).
            disc_rule_conds.
            assert (Some (obj_idx pobj) <> Some (obj_idx obj)) by congruence.
            solve_q; assumption.
          }
          { apply FirstMP_enqMsgs; assumption. }

      + apply InMP_enqMsgs_or in H30; destruct H30.
        1:{ exfalso.
            rewrite Forall_forall in H29; specialize (H29 _ H2).
            simpl in H29; rewrite H28 in H29; discriminate.
        }
        apply InMP_deqMP in H2.
        specialize (H0 H2).
        destruct (idx_dec (obj_idx obj) (obj_idx pobj)).
        * eapply obj_same_id_in_system_same in e; eauto; subst.
          destruct H0; [|dest; exfalso; red in H0; mred].
          right; split.
          { destruct (in_dec idx_dec down (idsOf routs)).
            { red; repeat (simpl; mred).
              intros; solve_q.
              destruct H16.
              apply in_map_iff in i; destruct i as [[down' rqdm] ?]; dest.
              simpl in *; subst.
              erewrite findQ_In_NoDup_enqMsgs; try eassumption.
              rewrite Forall_forall in H29; specialize (H29 _ H33); simpl in H29.
              rewrite filter_app; simpl.
              rewrite H29; simpl.
              destruct (filter _ _); discriminate.
            }
            { red; repeat (simpl; mred).
              intros; disc_rule_conds.
              elim n; clear n.
              eapply RqRsDownMatch_rs_rq in H17; [|eassumption].
              destruct H17 as [cidx [rdown ?]]; dest.
              disc_rule_conds.
            }
          }
          { apply FirstMP_enqMsgs.
            apply FirstMP_deqMP.
            { solve_midx_neq. }
            { eapply rsDown_rqsQ_nil_in_first with (cobj:= cobj); eauto.
              good_locking_get pobj.
              red in H21; mred.
              specialize (H21 _ H24).
              destruct H21 as [rdown [rsUp ?]]; dest.
              disc_rule_conds.
              apply H31.
            }
          }
        * destruct H0; [left; red; mred|].
          dest; right; split.
          { red in H0; red; mred.
            destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
            destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
            intros; specialize (H0 _ _ H21 H30 H31).
            disc_rule_conds.
            assert (Some (obj_idx pobj) <> Some (obj_idx obj)) by congruence.
            solve_q; assumption.
          }
          { apply FirstMP_enqMsgs.
            apply FirstMP_deqMP; [|assumption].
            solve_midx_neq.
          }

      + apply InMP_enqMsgs_or in H24; destruct H24.
        1:{ exfalso.
            rewrite Forall_forall in H29; specialize (H29 _ H11).
            simpl in H29; rewrite H22 in H29; discriminate.
        }
        apply InMP_deqMP in H11.
        specialize (H0 H11).
        destruct (idx_dec (obj_idx obj) (obj_idx pobj)).
        * eapply obj_same_id_in_system_same in e; eauto; subst.
          right; split.
          { destruct (in_dec idx_dec down (idsOf routs)).
            { red; repeat (simpl; mred).
              intros; solve_q.
              destruct H16.
              apply in_map_iff in i; destruct i as [[down' rqdm] ?]; dest.
              simpl in *; subst.
              erewrite findQ_In_NoDup_enqMsgs; try eassumption.
              rewrite Forall_forall in H29; specialize (H29 _ H31); simpl in H29.
              rewrite filter_app; simpl.
              rewrite H29; simpl.
              destruct (filter _ _); discriminate.
            }
            { red; repeat (simpl; mred).
              intros; disc_rule_conds.
              elim n; clear n.
              eapply RqRsDownMatch_rs_rq in H3; [|eassumption].
              destruct H3 as [cidx [rdown ?]]; dest.
              disc_rule_conds.
            }
          }
          { apply FirstMP_enqMsgs.
            apply FirstMP_deqMP.
            { apply parentIdxOf_not_eq in H17; [|apply Hsd].
              solve_midx_neq.
            }
            { eapply rsDown_rqsQ_nil_in_first with (cobj:= cobj); eauto.
              good_locking_get pobj.
              red in H23; mred.
              specialize (H23 _ H17).
              destruct H23 as [rdown [rsUp ?]]; dest.
              disc_rule_conds.
              apply H28.
            }
          }

        * destruct (idx_dec (obj_idx obj) (obj_idx cobj)).
          { eapply obj_same_id_in_system_same in e; eauto; subst.
            disc_rule_conds.
            exfalso; destruct H0.
            { good_locking_get pobj.
              eapply downLockInvORq_down_rqsQ_length_one_locked in H17; eauto;
                [|eapply rqsQ_length_ge_one; eauto;
                  apply FirstMP_InMP; auto].
              destruct H17 as [rqid ?]; dest.
              red in H0.
              destruct (orqs@[obj_idx pobj]) as [orq|]; simpl in *; [|discriminate].
              congruence.
            }
            { dest; pose proof (FirstMP_eq H20 H26).
              subst; simpl in *.
              rewrite H22 in H27; discriminate.
            }
          }
          { destruct H0; [left; red; mred|].
            dest; right; split.
            { red in H0; red; mred.
              destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
              destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
              intros; specialize (H0 _ _ H23 H24 H28).
              disc_rule_conds.
              assert (Some (obj_idx pobj) <> Some (obj_idx obj)) by congruence.
              solve_q; assumption.
            }
            { apply FirstMP_enqMsgs.
              apply FirstMP_deqMP; [|assumption].
              solve_midx_neq.
            }
          }

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + apply InMP_enqMP_or in H23; destruct H23.
        * dest; subst; disc_rule_conds.
          eapply obj_same_id_in_system_same in H23; eauto; subst.
          left; red; repeat (simpl; mred).
        * destruct (idx_dec (obj_idx obj) (obj_idx pobj)).
          { apply InMP_deqMP in H23.
            specialize (H0 H23).
            eapply obj_same_id_in_system_same in e; eauto; subst.
            destruct H0.
            { left; red in H0; red; repeat (simpl; mred). }
            { dest; right; split.
              { red in H0; red; mred. }
              { apply FirstMP_enqMP.
                apply FirstMP_deqMP; [|assumption].
                apply parentIdxOf_not_eq in H15; [|apply Hsd].
                solve_midx_neq.
              }
            }
          }
          { destruct (idx_dec (obj_idx obj) (obj_idx cobj)).
            { exfalso.
              eapply obj_same_id_in_system_same in e; eauto; subst.
              disc_rule_conds.
              eapply rsDown_in_deqMP_false
                with (cobj:= cobj) (rsdm1:= rmsg0) (rsdm2:= rsdm); eauto.
            }
            { apply InMP_deqMP in H23; specialize (H0 H23).
              destruct H0; [left; red in H0; red; mred|].
              dest; right; split.
              { red in H0; red; mred.
                destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
                destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
                intros; specialize (H0 _ _ H30 H31 H32).
                disc_rule_conds.
                assert (cidx <> obj_idx cobj)
                  by (intro Hx; subst; disc_rule_conds; auto).
                solve_q; assumption.
              }
              { apply FirstMP_enqMP.
                apply FirstMP_deqMP; [|assumption].
                solve_midx_neq.
              }
            }
          }

      + destruct (idx_dec (obj_idx obj) (obj_idx pobj)).
        * apply InMP_deqMP in H23.
          specialize (H0 H23).
          eapply obj_same_id_in_system_same in e; eauto; subst.
          destruct H0.
          { left; red in H0; red; repeat (simpl; mred). }
          { dest; right; split.
            { red in H0; red; mred. }
            { apply FirstMP_deqMP; [|assumption].
              apply parentIdxOf_not_eq in H15; [|apply Hsd].
              solve_midx_neq.
            }
          }
        * destruct (idx_dec (obj_idx obj) (obj_idx cobj)).
          { exfalso.
            eapply obj_same_id_in_system_same in e; eauto; subst.
            disc_rule_conds.
            eapply rsDown_in_deqMP_false
              with (cobj:= cobj) (rsdm1:= rmsg) (rsdm2:= rsdm); eauto.
          }
          { apply InMP_deqMP in H23; specialize (H0 H23).
            destruct H0; [left; red in H0; red; mred|].
            dest; right; split.
            { red in H0; red; mred.
              destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
              destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
              intros; specialize (H0 _ _ H27 H28 H29).
              disc_rule_conds.
              solve_q; assumption.
            }
            { apply FirstMP_deqMP; [|assumption].
              solve_midx_neq.
            }
          }

      + apply InMP_enqMP_or in H24; destruct H24.
        * dest; subst; disc_rule_conds.
          eapply obj_same_id_in_system_same in H20; eauto; subst.
          left; red; repeat (simpl; mred).
        * apply InMP_deqMsgs in H4.
          specialize (H0 H4).
          destruct (idx_dec (obj_idx obj) (obj_idx pobj)).
          { eapply obj_same_id_in_system_same in e; eauto; subst.
            left; red; repeat (simpl; mred).
          }
          { destruct H0.
            { left; red; repeat (simpl; mred). }
            { dest; right; split.
              { red in H0; red; mred.
                destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
                destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
                intros; specialize (H0 _ _ H30 H31 H32).
                disc_rule_conds.
                assert (obj_idx upCObj <> obj_idx cobj)
                  by (intro Hx; rewrite Hx in *; disc_rule_conds; auto).
                solve_q; assumption.
              }
              { apply FirstMP_enqMP.
                apply FirstMP_deqMsgs; [|eassumption].
                solve_midx_disj.
              }
            }
          }

      + apply InMP_enqMP_or in H24; destruct H24;
          [dest; subst; solve_midx_false|].
        apply InMP_deqMsgs in H24.
        specialize (H0 H24).
        destruct (idx_dec (obj_idx obj) (obj_idx pobj)).
        * eapply obj_same_id_in_system_same in e; eauto; subst.
          left; red; repeat (simpl; mred).
        * destruct H0.
          { left; red; repeat (simpl; mred). }
          { dest; right; split.
            { red in H0; red; mred.
              destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
              destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
              intros; specialize (H0 _ _ H27 H29 H30).
              disc_rule_conds.
              solve_q; assumption.
            }
            { apply FirstMP_enqMP.
              apply FirstMP_deqMsgs; [|eassumption].
              solve_midx_disj.
            }
          }

      + apply InMP_deqMsgs in H24.
        specialize (H0 H24).
        destruct (idx_dec (obj_idx obj) (obj_idx pobj)).
        * eapply obj_same_id_in_system_same in e; eauto; subst.
          left; red; repeat (simpl; mred).
        * destruct H0.
          { left; red; repeat (simpl; mred). }
          { dest; right; split.
            { red in H0; red; mred.
              destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
              destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
              intros; specialize (H0 _ _ H19 H25 H27).
              disc_rule_conds.
              solve_q; assumption.
            }
            { apply FirstMP_deqMsgs; [|eassumption].
              solve_midx_disj.
            }
          }

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      apply InMP_enqMsgs_or in H24; destruct H24.
      1:{ exfalso.
          rewrite Forall_forall in H23; specialize (H23 _ H24).
          simpl in H23; rewrite H22 in H23; discriminate.
      }

      destruct (idx_dec (obj_idx obj) (obj_idx pobj)).
      + apply InMP_deqMP in H24.
        specialize (H0 H24).
        eapply obj_same_id_in_system_same in e; eauto; subst.
        right; split.
        * destruct (in_dec idx_dec down (idsOf routs)).
          { red; repeat (simpl; mred).
            intros; solve_q.
            destruct H16.
            apply in_map_iff in i; destruct i as [[down' rqdm] ?]; dest.
            simpl in *; subst.
            erewrite findQ_In_NoDup_enqMsgs; try eassumption.
            rewrite Forall_forall in H23; specialize (H23 _ H38); simpl in H23.
            rewrite filter_app; simpl.
            rewrite H23; simpl.
            destruct (filter _ _); discriminate.
          }
          { red; repeat (simpl; mred).
            intros; disc_rule_conds.
            elim n; clear n.
            eapply RqRsDownMatch_rs_rq in H36; [|eassumption].
            destruct H36 as [cidx [rdown ?]]; dest.
            disc_rule_conds.
          }
        * apply FirstMP_enqMsgs.
          apply FirstMP_deqMP.
          { apply parentIdxOf_not_eq in H19; [|apply Hsd].
            solve_midx_neq.
          }
          { eapply rsDown_rqsQ_nil_in_first with (cobj:= cobj); eauto.
            good_locking_get pobj.
            red in H29; mred.
            specialize (H29 _ H19).
            destruct H29 as [rdown [rsUp ?]]; dest.
            disc_rule_conds.
            apply H35.
          }

      + destruct (idx_dec (obj_idx obj) (obj_idx cobj)).
        * eapply obj_same_id_in_system_same in e; eauto; subst.
          disc_rule_conds.
          exfalso.
          eapply rsDown_in_deqMP_false
            with (cobj:= cobj) (rsdm1:= rmsg) (rsdm2:= rsdm); eauto.
        * apply InMP_deqMP in H24.
          specialize (H0 H24).
          destruct H0; [left; red; mred|].
          dest; right; split.
          { red in H0; red; mred.
            destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
            destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
            intros; specialize (H0 _ _ H29 H31 H35).
            disc_rule_conds.
            assert (Some (obj_idx pobj) <> Some (obj_idx obj)) by congruence.
            solve_q; assumption.
          }
          { apply FirstMP_enqMsgs.
            apply FirstMP_deqMP; [|assumption].
            solve_midx_neq.
          }
  Qed.

  Lemma noRqRsDown_InvStep:
    InvStep sys step_m NoRqRsDown.
  Proof.
    red; intros.
    inv H1.
    - assumption.
    - apply noRqRsDown_step_ext_in; auto.
    - apply noRqRsDown_step_ext_out; auto.
    - eapply noRqRsDown_step_int; eauto.
      econstructor; eauto.
  Qed.

  Lemma noRqRsDown_ok:
    InvReachable sys step_m NoRqRsDown.
  Proof.
    eapply inv_reachable.
    - typeclasses eauto.
    - apply noRqRsDown_InvInit.
    - apply noRqRsDown_InvStep.
  Qed.

End RqRsDown.

Section Corollaries.
  Context `{dv: DecValue} `{oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System).
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hsd: RqRsDTree dtr sys)
             (Hrr: GoodRqRsSys dtr sys)
             (Hers: GoodExtRssSys sys).

  Corollary rqUp_in_rqUp_in_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall obj,
        In obj (sys_objs sys) ->
        forall rqUp,
          rqEdgeUpFrom dtr (obj_idx obj) = Some rqUp ->
          forall msgs rqum1 rqum2,
            st.(st_msgs) = msgs ->
            rqum1 <> rqum2 ->
            InMP rqUp rqum1 msgs ->
            InMP rqUp rqum2 msgs ->
            False.
  Proof.
    intros; subst.
    pose proof (upLockInv_ok Hiorqs Hrr Hsd H) as Hulinv.
    pose proof (rqEdgeUpFrom_Some (proj1 (proj2 Hsd)) _ H1).
    destruct H2 as [rsUp [down [pidx ?]]]; dest.
    good_locking_get obj.
    eapply upLockInvORq_rqUp_length_two_False; eauto.
    apply findQ_length_two with (midx:= rqUp) (msg1:= rqum1) (msg2:= rqum2);
      intuition congruence.
  Qed.

  Corollary rqUp_in_rsDown_in_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall obj,
        In obj (sys_objs sys) ->
        forall rqUp down,
          rqEdgeUpFrom dtr (obj_idx obj) = Some rqUp ->
          edgeDownTo dtr (obj_idx obj) = Some down ->
          forall msgs rqum rsdm,
            st.(st_msgs) = msgs ->
            InMP rqUp rqum msgs ->
            InMP down rsdm msgs ->
            rsdm.(msg_type) = MRs ->
            False.
  Proof.
    intros; subst.
    pose proof (upLockInv_ok Hiorqs Hrr Hsd H) as Hulinv.
    pose proof (rqEdgeUpFrom_Some (proj1 (proj2 Hsd)) _ H1).
    destruct H3 as [rsUp [rdown [pidx ?]]]; dest.
    disc_rule_conds.
    good_locking_get obj.
    eapply upLockInvORq_rqUp_down_rssQ_False; eauto.
    - eapply findQ_length_ge_one; eauto.
    - eapply rssQ_length_ge_one; eauto.
  Qed.

  Corollary rqUp_parent_locked_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall obj,
        In obj (sys_objs sys) ->
        forall rqUp pidx down,
          rqEdgeUpFrom dtr (obj_idx obj) = Some rqUp ->
          parentIdxOf dtr (obj_idx obj) = Some pidx ->
          edgeDownTo dtr (obj_idx obj) = Some down ->
          forall msgs rqum,
            st.(st_msgs) = msgs ->
            InMP rqUp rqum msgs ->
            forall orqs,
              st.(st_orqs) = orqs ->
              OLockedTo orqs pidx (Some down) ->
              False.
  Proof.
    intros; subst.
    pose proof (upLockInv_ok Hiorqs Hrr Hsd H) as Hulinv.
    good_locking_get obj.
    assert (UpLockedInv dtr st.(st_orqs) st.(st_msgs) obj.(obj_idx))
      by (eapply upLockInvORq_parent_locked_locked; eauto).
    red in H6.
    destruct H6 as [rrqUp [rdown [rpidx ?]]]; dest.
    disc_rule_conds.
    xor3_contra2 H13.
    red in H5.
    destruct (findQ rrqUp (st_msgs st)) as [|e q]; [dest_in|].
    destruct q; [reflexivity|simpl in H10; lia].
  Qed.

  Corollary rsDown_in_rsDown_in_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall obj,
        In obj (sys_objs sys) ->
        forall down,
          edgeDownTo dtr (obj_idx obj) = Some down ->
          forall msgs rsdm1 rsdm2,
            st.(st_msgs) = msgs ->
            rsdm1 <> rsdm2 ->
            InMP down rsdm1 msgs ->
            rsdm1.(msg_type) = MRs ->
            InMP down rsdm2 msgs ->
            rsdm2.(msg_type) = MRs ->
            False.
  Proof.
    intros; subst.
    pose proof (upLockInv_ok Hiorqs Hrr Hsd H) as Hulinv.
    pose proof (edgeDownTo_Some (proj1 (proj2 Hsd)) _ H1).
    destruct H2 as [rqUp [rsUp [pidx ?]]]; dest.
    good_locking_get obj.
    eapply upLockInvORq_down_rssQ_length_two_False; eauto.
    apply rssQ_length_two with (midx:= down) (msg1:= rsdm1) (msg2:= rsdm2); eauto.
  Qed.

  Corollary rsDown_in_length_two_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall obj,
        In obj (sys_objs sys) ->
        forall down,
          edgeDownTo dtr (obj_idx obj) = Some down ->
          forall msgs,
            st.(st_msgs) = msgs ->
            length (rssQ msgs down) >= 2 -> False.
  Proof.
    intros; subst.
    pose proof (upLockInv_ok Hiorqs Hrr Hsd H) as Hulinv.
    pose proof (edgeDownTo_Some (proj1 (proj2 Hsd)) _ H1).
    destruct H2 as [rqUp [rsUp [pidx ?]]]; dest.
    good_locking_get obj.
    eapply upLockInvORq_down_rssQ_length_two_False; eauto.
  Qed.

  Corollary rsDown_parent_locked_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall obj,
        In obj (sys_objs sys) ->
        forall pidx down,
          parentIdxOf dtr (obj_idx obj) = Some pidx ->
          edgeDownTo dtr (obj_idx obj) = Some down ->
          forall msgs rsdm,
            st.(st_msgs) = msgs ->
            InMP down rsdm msgs ->
            rsdm.(msg_type) = MRs ->
            forall orqs,
              st.(st_orqs) = orqs ->
              OLockedTo orqs pidx (Some down) ->
              False.
  Proof.
    intros; subst.
    pose proof (upLockInv_ok Hiorqs Hrr Hsd H) as Hulinv.
    good_locking_get obj.
    assert (UpLockedInv dtr st.(st_orqs) st.(st_msgs) obj.(obj_idx))
      by (eapply upLockInvORq_parent_locked_locked; eauto).
    red in H6.
    destruct H6 as [rqUp [rdown [rpidx ?]]]; dest.
    disc_rule_conds.
    xor3_contra3 H13.
    apply rssQ_length_ge_one in H4; [|assumption].
    lia.
  Qed.

  Corollary upLockFree_parent_locked_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall obj,
        In obj (sys_objs sys) ->
        forall pidx down,
          parentIdxOf dtr (obj_idx obj) = Some pidx ->
          edgeDownTo dtr (obj_idx obj) = Some down ->
          forall orqs orq,
            st.(st_orqs) = orqs ->
            orqs@[obj_idx obj] = Some orq ->
            orq@[upRq] = None ->
            OLockedTo orqs pidx (Some down) ->
            False.
  Proof.
    intros; subst.
    pose proof (upLockInv_ok Hiorqs Hrr Hsd H) as Hulinv.
    good_locking_get obj.
    revert H5.
    eapply upLockInvORq_parent_locked_locked; eauto.
    rewrite H4 in H3; eassumption.
  Qed.

  Corollary upLockFree_rqUp_in_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall obj,
        In obj (sys_objs sys) ->
        forall orqs orq,
          st.(st_orqs) = orqs ->
          orqs@[obj_idx obj] = Some orq ->
          orq@[upRq] = None ->
          forall rqUp,
            rqEdgeUpFrom dtr (obj_idx obj) = Some rqUp ->
            forall msgs rqum,
            st.(st_msgs) = msgs ->
            InMP rqUp rqum msgs ->
            False.
  Proof.
    intros; subst.
    pose proof (upLockInv_ok Hiorqs Hrr Hsd H) as Hulinv.
    pose proof (rqEdgeUpFrom_Some (proj1 (proj2 Hsd)) _ H4).
    destruct H1 as [rsUp [down [pidx ?]]]; dest.
    good_locking_get obj.
    eapply upLockInvORq_rqUp_length_one_locked in H8; eauto.
    - dest; mred.
    - eapply findQ_length_ge_one; eauto.
  Qed.

  Corollary upLockFree_rsDown_in_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall obj,
        In obj (sys_objs sys) ->
        forall orqs orq,
          st.(st_orqs) = orqs ->
          orqs@[obj_idx obj] = Some orq ->
          orq@[upRq] = None ->
          forall down,
            edgeDownTo dtr (obj_idx obj) = Some down ->
            forall msgs rsdm,
              st.(st_msgs) = msgs ->
              rsdm.(msg_type) = MRs ->
              InMP down rsdm msgs ->
              False.
  Proof.
    intros; subst.
    pose proof (upLockInv_ok Hiorqs Hrr Hsd H) as Hulinv.
    pose proof (edgeDownTo_Some (proj1 (proj2 Hsd)) _ H4).
    destruct H1 as [rqUp [rsUp [pidx ?]]]; dest.
    good_locking_get obj.
    eapply upLockInvORq_down_rssQ_length_one_locked in H9; eauto.
    - dest; mred.
    - eapply rssQ_length_ge_one; eauto.
  Qed.

  Corollary rsDown_in_rqDown_first_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall cobj pobj,
        In cobj (sys_objs sys) ->
        In pobj (sys_objs sys) ->
        parentIdxOf dtr (obj_idx cobj) = Some (obj_idx pobj) ->
        forall down,
          edgeDownTo dtr (obj_idx cobj) = Some down ->
          forall msgs rsdm rqdm,
            st.(st_msgs) = msgs ->
            msg_type rsdm = MRs ->
            InMP down rsdm msgs ->
            msg_type rqdm = MRq ->
            FirstMP msgs down rqdm ->
            False.
  Proof.
    intros; subst.
    pose proof (downLockInv_ok Hiorqs Hrr Hsd Hers H) as Hdlinv.
    pose proof (noRqRsDown_ok Hiorqs Hrr Hsd Hers H) as Hrrinv.
    red in Hrrinv.
    specialize (Hrrinv _ _ H0 H1 H2 _ H3 _ H5 H6).
    destruct Hrrinv.
    - good_locking_get pobj.
      assert (DownLockFreeInv dtr (st_orqs st) (st_msgs st) (obj_idx pobj)).
      { red in H4, H9.
        destruct ((st_orqs st)@[obj_idx pobj]) eqn:Horq; simpl in *.
        { rewrite H4 in H9; assumption. }
        { assumption. }
      }
      specialize (H10 _ H2); destruct H10 as [rdown [rsUp ?]]; dest.
      repeat disc_rule_minds.
      red in H12; dest.
      apply FirstMP_InMP in H8.
      apply rqsQ_length_ge_one in H8; [|assumption].
      rewrite H10 in H8; simpl in H8; lia.
    - dest.
      pose proof (FirstMP_eq H8 H9); subst.
      rewrite H5 in H7; discriminate.
  Qed.

  Corollary rqDown_in_rsDown_push_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall cobj pobj,
        In cobj (sys_objs sys) ->
        In pobj (sys_objs sys) ->
        parentIdxOf dtr (obj_idx cobj) = Some (obj_idx pobj) ->
        forall down,
          edgeDownTo dtr (obj_idx cobj) = Some down ->
          forall msgs dq rqdm rsdm,
            st.(st_msgs) = msgs ->
            msg_type rqdm = MRq ->
            In rqdm dq ->
            msg_type rsdm = MRs ->
            findQ down msgs = dq ++ [rsdm] ->
            False.
  Proof.
    intros; subst.
    pose proof (upLockInv_ok Hiorqs Hrr Hsd H) as Hulinv.
    pose proof (downLockInv_ok Hiorqs Hrr Hsd Hers H) as Hdlinv.
    pose proof (noRqRsDown_ok Hiorqs Hrr Hsd Hers H) as Hrrinv.
    assert (InMP down rsdm st.(st_msgs)).
    { red; rewrite H8.
      apply in_or_app; right; left; reflexivity.
    }

    red in Hrrinv.
    specialize (Hrrinv _ _ H0 H1 H2 _ H3 _ H7 H4); clear H4.
    destruct Hrrinv; dest.
    - good_locking_get pobj.
      eapply downLockInvORq_down_rqsQ_length_one_locked in H10; eauto;
        [|eapply rqsQ_length_ge_one; eauto;
          red; rewrite H8; apply in_or_app; left; assumption].
      destruct H10 as [rqid ?]; dest.
      red in H4.
      destruct ((st_orqs st)@[obj_idx pobj]) eqn:Horq; [simpl in *|discriminate].
      destruct (o@[downRq]) eqn:Hrqid; [simpl in *|discriminate].
      discriminate.
    - good_locking_get cobj.
      eapply upLockInvORq_down_rssQ_length_two_False in H10; eauto.
      unfold rssQ; rewrite H8.
      rewrite filter_app; simpl.
      rewrite H7; simpl.
      rewrite app_length; simpl.
      unfold FirstMP, firstMP in H9.
      rewrite H8 in H9.
      destruct dq as [|dmsg dq]; [elim H6|].
      simpl in H9; inv H9.
      simpl; rewrite H7; simpl.
      lia.
  Qed.

  Corollary rsDown_in_rsUp_in_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall cobj pobj,
        In cobj (sys_objs sys) ->
        In pobj (sys_objs sys) ->
        parentIdxOf dtr (obj_idx cobj) = Some (obj_idx pobj) ->
        forall down rsUp,
          edgeDownTo dtr (obj_idx cobj) = Some down ->
          rsEdgeUpFrom dtr (obj_idx cobj) = Some rsUp ->
          forall msgs rsdm rsum,
            st.(st_msgs) = msgs ->
            msg_type rsdm = MRs ->
            InMP down rsdm msgs ->
            InMP rsUp rsum msgs ->
            False.
  Proof.
    intros; subst.
    pose proof (downLockInv_ok Hiorqs Hrr Hsd Hers H) as Hdlinv.
    pose proof (noRqRsDown_ok Hiorqs Hrr Hsd Hers H) as Hrrinv.
    red in Hrrinv.
    specialize (Hrrinv _ _ H0 H1 H2 _ H3 _ H6 H7).
    destruct Hrrinv.
    - good_locking_get pobj.
      assert (DownLockFreeInv dtr (st_orqs st) (st_msgs st) (obj_idx pobj)).
      { red in H5, H9.
        destruct ((st_orqs st)@[obj_idx pobj]) eqn:Horq; simpl in *.
        { rewrite H5 in H9; assumption. }
        { assumption. }
      }
      specialize (H10 _ H2); destruct H10 as [rdown [rrsUp ?]]; dest.
      repeat disc_rule_minds.
      red in H12; dest.
      apply findQ_length_ge_one in H8.
      rewrite H11 in H8; simpl in H8; lia.
    - dest.
      good_locking_get pobj.
      eapply downLockInvORq_rsUp_length_one_locked in H10; eauto;
        [|eapply findQ_length_ge_one; eassumption].
      destruct H10 as [rqid ?]; dest.
      red in H5.
      destruct ((st_orqs st)@[obj_idx pobj]) eqn:Horq; [simpl in *|exfalso; auto].
      destruct (o@[downRq]) eqn:Hrqid; [simpl in *|exfalso; auto].
      inv H10.
      specialize (H5 _ _ H3 H4 H12).
      specialize (H11 _ H2); destruct H11 as [rdown [rrsUp ?]]; dest.
      repeat disc_rule_minds.
      destruct (in_dec _ _ _); auto.
      red in H13; dest.
      xor3_contra1 H13.
      + destruct (rqsQ (st_msgs st) rdown); [exfalso; auto|].
        simpl in *; lia.
      + apply findQ_length_ge_one in H8.
        lia.
  Qed.

  Corollary rqDown_in_rqDown_in_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall pobj,
        In pobj (sys_objs sys) ->
        forall oidx rqDown,
          parentIdxOf dtr oidx = Some (obj_idx pobj) ->
          edgeDownTo dtr oidx = Some rqDown ->
          forall msgs rqdm1 rqdm2,
            st.(st_msgs) = msgs ->
            rqdm1 <> rqdm2 ->
            InMP rqDown rqdm1 msgs ->
            rqdm1.(msg_type) = MRq ->
            InMP rqDown rqdm2 msgs ->
            rqdm2.(msg_type) = MRq ->
            False.
  Proof.
    intros; subst.
    pose proof (downLockInv_ok Hiorqs Hrr Hsd Hers H) as Hdlinv.
    good_locking_get pobj.
    eapply downLockInvORq_down_rqsQ_length_two_False; eauto.
    apply rqsQ_length_two with (midx:= rqDown) (msg1:= rqdm1) (msg2:= rqdm2);
      intuition congruence.
  Qed.

  Corollary rqDown_in_rsUp_in_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall pobj,
        In pobj (sys_objs sys) ->
        forall oidx rqDown rsUp,
          parentIdxOf dtr oidx = Some (obj_idx pobj) ->
          edgeDownTo dtr oidx = Some rqDown ->
          rsEdgeUpFrom dtr oidx = Some rsUp ->
          forall msgs rqdm rsum,
            st.(st_msgs) = msgs ->
            InMP rqDown rqdm msgs ->
            rqdm.(msg_type) = MRq ->
            InMP rsUp rsum msgs ->
            False.
  Proof.
    intros; subst.
    pose proof (downLockInv_ok Hiorqs Hrr Hsd Hers H) as Hdlinv.
    good_locking_get pobj.
    eapply downLockInvORq_down_rqsQ_rsUp_False; eauto.
    - eapply rqsQ_length_ge_one; eauto.
    - eapply findQ_length_ge_one; eauto.
  Qed.

  Corollary rsUp_in_rsUp_in_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall pobj,
        In pobj (sys_objs sys) ->
        forall oidx rsUp,
          parentIdxOf dtr oidx = Some (obj_idx pobj) ->
          rsEdgeUpFrom dtr oidx = Some rsUp ->
          forall msgs rsum1 rsum2,
            st.(st_msgs) = msgs ->
            rsum1 <> rsum2 ->
            InMP rsUp rsum1 msgs ->
            InMP rsUp rsum2 msgs ->
            False.
  Proof.
    intros; subst.
    pose proof (downLockInv_ok Hiorqs Hrr Hsd Hers H) as Hdlinv.
    good_locking_get pobj.
    eapply downLockInvORq_rsUp_length_two_False; eauto.
    apply findQ_length_two with (midx:= rsUp) (msg1:= rsum1) (msg2:= rsum2);
      intuition congruence.
  Qed.

  Corollary rsUp_in_length_two_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall pobj,
        In pobj (sys_objs sys) ->
        forall oidx rsUp,
          parentIdxOf dtr oidx = Some (obj_idx pobj) ->
          rsEdgeUpFrom dtr oidx = Some rsUp ->
          forall msgs,
            st.(st_msgs) = msgs ->
            length (findQ rsUp msgs) >= 2 -> False.
  Proof.
    intros; subst.
    pose proof (downLockInv_ok Hiorqs Hrr Hsd Hers H) as Hdlinv.
    good_locking_get pobj.
    eapply downLockInvORq_rsUp_length_two_False; eauto.
  Qed.

  Corollary downLockFree_rqDown_in_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall pobj,
        In pobj (sys_objs sys) ->
        forall orqs porq,
          st.(st_orqs) = orqs ->
          orqs@[obj_idx pobj] = Some porq ->
          porq@[downRq] = None ->
          forall oidx rqDown,
            parentIdxOf dtr oidx = Some (obj_idx pobj) ->
            edgeDownTo dtr oidx = Some rqDown ->
            forall msgs rqdm,
              st.(st_msgs) = msgs ->
              InMP rqDown rqdm msgs ->
              rqdm.(msg_type) = MRq ->
              False.
  Proof.
    intros; subst.
    pose proof (downLockInv_ok Hiorqs Hrr Hsd Hers H) as Hdlinv.
    good_locking_get pobj.
    eapply downLockInvORq_down_rqsQ_length_one_locked in H1; eauto;
      [|eapply rqsQ_length_ge_one; eassumption].
    destruct H1 as [rqid ?]; dest.
    disc_rule_conds.
  Qed.

  Corollary downLockFree_rsUp_in_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall pobj,
        In pobj (sys_objs sys) ->
        forall orqs porq,
          st.(st_orqs) = orqs ->
          orqs@[obj_idx pobj] = Some porq ->
          porq@[downRq] = None ->
          forall oidx rsUp,
            parentIdxOf dtr oidx = Some (obj_idx pobj) ->
            rsEdgeUpFrom dtr oidx = Some rsUp ->
            forall msgs rsum,
              st.(st_msgs) = msgs ->
              InMP rsUp rsum msgs ->
              False.
  Proof.
    intros; subst.
    pose proof (downLockInv_ok Hiorqs Hrr Hsd Hers H) as Hdlinv.
    good_locking_get pobj.
    eapply downLockInvORq_rsUp_length_one_locked in H1; eauto;
      [|eapply findQ_length_ge_one; eassumption].
    destruct H1 as [rqid ?]; dest.
    disc_rule_conds.
  Qed.

  Corollary downLockFree_child_lock_to_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall pobj,
        In pobj (sys_objs sys) ->
        forall orqs porq,
          st.(st_orqs) = orqs ->
          orqs@[obj_idx pobj] = Some porq ->
          porq@[downRq] = None ->
          forall oidx rsUp orq rqid,
            parentIdxOf dtr oidx = Some (obj_idx pobj) ->
            rsEdgeUpFrom dtr oidx = Some rsUp ->
            orqs@[oidx] = Some orq ->
            orq@[downRq] = Some rqid ->
            rqid.(rqi_midx_rsb) = Some rsUp ->
            False.
  Proof.
    intros; subst.
    pose proof (downLockInv_ok Hiorqs Hrr Hsd Hers H) as Hdlinv.
    good_locking_get pobj.
    red in H1; disc_rule_conds.
    specialize (H1 _ H4).
    destruct H1 as [down [rrsUp ?]]; dest.
    disc_rule_conds.
    red in H10; dest.
    red in H11; disc_rule_conds.
  Qed.

End Corollaries.

Close Scope list.
Close Scope fmap.
