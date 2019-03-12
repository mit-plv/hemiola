Require Import Peano_dec Omega List ListSupport.
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
        specialize (H (in_map _ _ _ Ho)); dest
      end;
  try match goal with
      | [Hlock: DownLockInv _ ?sys _, Ho: In obj (sys_objs ?sys) |- _] =>
        let H := fresh "H" in
        pose proof Hlock as H;
        specialize (H (obj_idx obj)); simpl in H;
        specialize (H (in_map _ _ _ Ho)); dest
      end.

Ltac disc_lock_conds :=
  match goal with
  | [H: OLockedTo _ _ _ |- _] => red in H
  | [H: UpLockInvORq _ _ _ _ _ |- _] => red in H; mred; simpl in H; mred
  | [H: UpLockedInv _ _ _ _ |- _] =>
    let rqUp := fresh "rqUp" in
    let down := fresh "down" in
    let pidx := fresh "pidx" in
    destruct H as [rqUp [down [pidx ?]]]; dest
  end.

Section RqRsDown.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypothesis (Hrrs: RqRsSys dtr sys).

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
                   In rsUp rqid.(rqi_minds_rss) ->
                   rqsQ msgs down <> nil)).
  
  Definition NoRqRsDown (st: MState oifc) :=
    forall cobj pobj,
      In cobj sys.(sys_objs) ->
      In pobj sys.(sys_objs) ->
      parentIdxOf dtr (obj_idx cobj) = Some (obj_idx pobj) ->
      forall down,
        edgeDownTo dtr (obj_idx cobj) = Some down ->
        forall rsdm,
          rsdm.(msg_type) = MRs ->
          InMP down rsdm st.(bst_msgs) ->
          ONoDownLock st.(bst_orqs) (obj_idx pobj) \/
          (ODownRq st.(bst_orqs) st.(bst_msgs) (obj_idx pobj) down /\
           FirstMP st.(bst_msgs) down rsdm).
  
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
      NoRqRsDown {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eins <> nil ->
      ValidMsgsExtIn sys eins ->
      NoRqRsDown {| bst_oss := oss;
                    bst_orqs := orqs;
                    bst_msgs := enqMsgs eins msgs |}.
  Proof.
    intros; disc_NoRqRsDown.
    assert (~ In down (idsOf eins)).
    { destruct H1.
      apply DisjList_In_1 with (l2:= sys_minds sys).
      { eapply DisjList_SubList; eauto.
        apply DisjList_comm.
        apply sys_minds_sys_merqs_DisjList.
      }
      { eapply rqrsDTree_edgeDownTo_sys_minds; [apply Hrrs|].
        eassumption.
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
      NoRqRsDown {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eouts <> nil ->
      Forall (FirstMPI msgs) eouts ->
      ValidMsgsExtOut sys eouts ->
      NoRqRsDown {| bst_oss := oss;
                    bst_orqs := orqs;
                    bst_msgs := deqMsgs (idsOf eouts) msgs |}.
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
      { eapply rqrsDTree_edgeDownTo_sys_minds; [apply Hrrs|].
        eassumption.
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
          st.(bst_msgs) = msgs ->
          edgeDownTo dtr (obj_idx cobj) = Some down ->
          rsdm.(msg_type) = MRs ->
          InMP down rsdm msgs ->
          rqsQ msgs down = nil ->
          FirstMP msgs down rsdm.
  Proof.
    destruct Hrrs as [? [? ?]]; intros; subst.
    pose proof (upLockInv_ok H0 H H2).
    good_locking_get cobj.
    pose proof (edgeDownTo_Some H _ H5).
    destruct H10 as [rqUp [rsUp [pidx ?]]]; dest.
    eapply upLockInvORq_down_rssQ_length_one_locked in H9; eauto;
      [|eapply rssQ_length_ge_one; eauto].
    destruct H9 as [rrqUp [rdown [rpidx ?]]]; dest.
    repeat disc_rule_minds.
    apply InMP_FirstMP; [assumption|].
    rewrite rqsQ_rssQ_length.
    rewrite H8; simpl.
    assumption.
  Qed.

  Lemma rsDown_in_deqMP_false:
    forall st,
      Reachable (steps step_m) sys st ->
      forall cobj,
        In cobj sys.(sys_objs) ->
        forall msgs down rsdm1 rsdm2,
          st.(bst_msgs) = msgs ->
          edgeDownTo dtr (obj_idx cobj) = Some down ->
          rsdm1.(msg_type) = MRs ->
          FirstMP msgs down rsdm1 ->
          rsdm2.(msg_type) = MRs ->
          InMP down rsdm2 (deqMP down msgs) ->
          False.
  Proof.
    destruct Hrrs as [? [? ?]]; intros; subst.
    pose proof (upLockInv_ok H0 H H2).
    good_locking_get cobj.
    pose proof (edgeDownTo_Some H _ H5).
    destruct H11 as [rqUp [rsUp [pidx ?]]]; dest.
    eapply upLockInvORq_down_rssQ_length_one_locked in H10; eauto.
    - red in H10.
      destruct H10 as [rrqUp [rdown [rpidx ?]]]; dest.
      repeat disc_rule_minds.

      (* Looks it is too specific to extract as a lemma. *)
      clear -H6 H7 H8 H9 H17.
      unfold InMP, FirstMP, firstMP, rssQ, deqMP in *.
      destruct (findQ rdown (bst_msgs st)); [discriminate|].
      simpl in H7; inv H7.
      simpl in H17; rewrite H6 in H17; simpl in H17.
      unfold findQ in H9; mred; simpl in H9.
      destruct (filter (fun msg => msg_type msg) q) eqn:Hq.
      + assert (In rsdm2 (filter (fun msg => msg_type msg) q)).
        { apply filter_In.
          split; auto.
        }
        rewrite Hq in H; elim H.
      + simpl in H17; omega.
    - eapply rssQ_length_ge_one; eauto.
      eapply InMP_deqMP; eassumption.
  Qed.

  Lemma noRqRsDown_step_int:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      NoRqRsDown st1 ->
      forall oidx ridx rins routs st2,
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        NoRqRsDown st2.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H2) as Hftinv.
    assert (Reachable (steps step_m) sys st2) as Hnrch
      by (eapply reachable_steps; [eassumption|apply steps_singleton; eassumption]).
    pose proof (upLockInv_ok H0 H Hnrch) as Hulinv.
    pose proof (downLockInv_ok H0 H H2) as Hdlinv.
    clear Hnrch.

    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      destruct (eq_nat_dec (obj_idx obj) (obj_idx pobj)).
      + eapply obj_same_id_in_system_same in e; eauto; subst.
        left; red; mred.
      + apply InMP_enqMP_or in H11; destruct H11;
          [exfalso; dest; subst; disc_rule_conds; auto|].
        apply InMP_deqMP in H11.
        specialize (H3 H11); destruct H3.
        * left; red; mred.
        * dest; right; split.
          { red in H3; red; mred.
            destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
            destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
            intros; specialize (H3 _ _ H20 H23 H27).
            assert (cidx <> cidx0) by (intro Hx; subst; disc_rule_conds; auto).
            solve_q; assumption.
          }
          { apply FirstMP_enqMP.
            apply FirstMP_deqMP; [|assumption].
            solve_midx_neq.
          }

    - disc_rule_conds.
      destruct (eq_nat_dec (obj_idx obj) (obj_idx pobj)).
      + eapply obj_same_id_in_system_same in e; eauto; subst.
        left; red; mred.
      + apply InMP_enqMP_or in H18; destruct H18;
          [exfalso; dest; subst; solve_midx_false|].
        apply InMP_deqMP in H14; specialize (H3 H14).
        destruct (eq_nat_dec (obj_idx cobj) (obj_idx obj)).
        * exfalso.
          eapply obj_same_id_in_system_same in e; eauto; subst.
          disc_rule_conds.
          destruct H3.
          { good_locking_get pobj.
            eapply downLockInvORq_down_rqsQ_length_one_locked in H6; eauto;
              [|eapply rqsQ_length_ge_one; eauto;
                apply FirstMP_InMP; auto].
            destruct H6 as [rqid ?]; dest.
            red in H3.
            destruct (orqs@[obj_idx pobj]) as [orq|]; simpl in *; [|discriminate].
            congruence.
          }
          { dest; pose proof (FirstMP_eq H7 H24).
            subst; simpl in *.
            rewrite H8 in H27; discriminate.
          }
        * destruct H3; [left; red; mred|].
          dest; right; split.
          { red in H3; red; mred.
            destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
            destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
            intros; specialize (H3 _ _ H20 H22 H26).
            solve_q; assumption.
          }
          { apply FirstMP_enqMP.
            apply FirstMP_deqMP; [|assumption].
            solve_midx_neq.
          }

    - disc_rule_conds.
      + apply InMP_enqMP_or in H31; destruct H31;
          [exfalso; dest; subst; disc_rule_conds; auto|].
        apply InMP_deqMP in H14.
        specialize (H3 H14).
        destruct (eq_nat_dec (obj_idx obj) (obj_idx pobj)).
        * eapply obj_same_id_in_system_same in e; eauto; subst.
          destruct H3.
          { left; red in H3; red; repeat (simpl; mred). }
          { dest; right; split.
            { red in H3; red; repeat (simpl; mred).
              destruct (porq@[downRq]) eqn:Hrqid; simpl in *; auto.
              intros; specialize (H3 _ _ H26 H31 H34).
              solve_q; assumption.
            }
            { apply FirstMP_enqMP.
              apply FirstMP_deqMP; [|assumption].
              solve_midx_neq.
            }
          }
        * destruct H3.
          { left; red in H3; red; mred. }
          { dest; right; split.
            { red in H3; red; mred.
              destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
              destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
              intros; specialize (H3 _ _ H26 H31 H34).
              solve_q; assumption.
            }
            { apply FirstMP_enqMP.
              apply FirstMP_deqMP; [|assumption].
              solve_midx_neq.
            }
          }

      + apply InMP_enqMsgs_or in H33; destruct H33.
        1:{ exfalso.
            rewrite Forall_forall in H32; specialize (H32 _ H5).
            simpl in H32; rewrite H31 in H32; discriminate.
        }
        apply InMP_deqMP in H5.
        specialize (H3 H5).
        destruct (eq_nat_dec (obj_idx obj) (obj_idx pobj)).
        * eapply obj_same_id_in_system_same in e; eauto; subst.
          destruct H3; [|dest; exfalso; red in H3; mred].
          right; split.
          { destruct (in_dec eq_nat_dec down (idsOf routs)).
            { red; repeat (simpl; mred).
              intros; solve_q.
              destruct H19.
              apply in_map_iff in i; destruct i as [[down' rqdm] ?]; dest.
              simpl in *; subst.
              erewrite findQ_In_NoDup_enqMsgs; try eassumption.
              rewrite Forall_forall in H32; specialize (H32 _ H36); simpl in H32.
              rewrite filter_app; simpl.
              rewrite H32; simpl.
              destruct (filter _ _); discriminate.
            }
            { red; repeat (simpl; mred).
              intros; disc_rule_conds.
              elim n; clear n.
              eapply RqRsDownMatch_rs_rq in H20; [|eassumption].
              destruct H20 as [cidx [rdown ?]]; dest.
              disc_rule_conds.
            }
          }
          { apply FirstMP_enqMsgs.
            apply FirstMP_deqMP.
            { solve_midx_neq. }
            { eapply rsDown_rqsQ_nil_in_first with (cobj:= cobj); eauto.
              good_locking_get pobj.
              red in H24; mred.
              specialize (H24 _ H27).
              destruct H24 as [rdown [rsUp ?]]; dest.
              disc_rule_conds.
              apply H34.
            }
          }
        * destruct H3; [left; red; mred|].
          dest; right; split.
          { red in H3; red; mred.
            destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
            destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
            intros; specialize (H3 _ _ H24 H33 H34).
            disc_rule_conds.
            assert (Some (obj_idx pobj) <> Some (obj_idx obj)) by congruence.
            solve_q; assumption.
          }
          { apply FirstMP_enqMsgs.
            apply FirstMP_deqMP; [|assumption].
            solve_midx_neq.
          }

      + apply InMP_enqMsgs_or in H27; destruct H27.
        1:{ exfalso.
            rewrite Forall_forall in H32; specialize (H32 _ H14).
            simpl in H32; rewrite H25 in H32; discriminate.
        }
        apply InMP_deqMP in H14.
        specialize (H3 H14).
        destruct (eq_nat_dec (obj_idx obj) (obj_idx pobj)).
        * eapply obj_same_id_in_system_same in e; eauto; subst.
          right; split.
          { destruct (in_dec eq_nat_dec down (idsOf routs)).
            { red; repeat (simpl; mred).
              intros; solve_q.
              destruct H19.
              apply in_map_iff in i; destruct i as [[down' rqdm] ?]; dest.
              simpl in *; subst.
              erewrite findQ_In_NoDup_enqMsgs; try eassumption.
              rewrite Forall_forall in H32; specialize (H32 _ H34); simpl in H32.
              rewrite filter_app; simpl.
              rewrite H32; simpl.
              destruct (filter _ _); discriminate.
            }
            { red; repeat (simpl; mred).
              intros; disc_rule_conds.
              elim n; clear n.
              eapply RqRsDownMatch_rs_rq in H6; [|eassumption].
              destruct H6 as [cidx [rdown ?]]; dest.
              disc_rule_conds.
            }
          }
          { apply FirstMP_enqMsgs.
            apply FirstMP_deqMP.
            { apply parentIdxOf_not_eq in H20; [|apply Hrrs].
              solve_midx_neq.
            }
            { eapply rsDown_rqsQ_nil_in_first with (cobj:= cobj); eauto.
              good_locking_get pobj.
              red in H26; mred.
              specialize (H26 _ H20).
              destruct H26 as [rdown [rsUp ?]]; dest.
              disc_rule_conds.
              apply H31.
            }
          }
          
        * destruct (eq_nat_dec (obj_idx obj) (obj_idx cobj)).
          { eapply obj_same_id_in_system_same in e; eauto; subst.
            disc_rule_conds.
            exfalso; destruct H3.
            { good_locking_get pobj.
              eapply downLockInvORq_down_rqsQ_length_one_locked in H20; eauto;
                [|eapply rqsQ_length_ge_one; eauto;
                  apply FirstMP_InMP; auto].
              destruct H20 as [rqid ?]; dest.
              red in H3.
              destruct (orqs@[obj_idx pobj]) as [orq|]; simpl in *; [|discriminate].
              congruence.
            }
            { dest; pose proof (FirstMP_eq H23 H29).
              subst; simpl in *.
              rewrite H25 in H30; discriminate.
            }
          }
          { destruct H3; [left; red; mred|].
            dest; right; split.
            { red in H3; red; mred.
              destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
              destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
              intros; specialize (H3 _ _ H26 H27 H31).
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
      + apply InMP_enqMP_or in H26; destruct H26.
        * dest; subst; disc_rule_conds.
          eapply obj_same_id_in_system_same in H26; eauto; subst.
          left; red; repeat (simpl; mred).
        * destruct (eq_nat_dec (obj_idx obj) (obj_idx pobj)).
          { apply InMP_deqMP in H26.
            specialize (H3 H26).
            eapply obj_same_id_in_system_same in e; eauto; subst.
            destruct H3.
            { left; red in H3; red; repeat (simpl; mred). }
            { dest; right; split.
              { red in H3; red; mred. }
              { apply FirstMP_enqMP.
                apply FirstMP_deqMP; [|assumption].
                apply parentIdxOf_not_eq in H18; [|apply Hrrs].
                solve_midx_neq.
              }
            }
          }
          { destruct (eq_nat_dec (obj_idx obj) (obj_idx cobj)).
            { exfalso.
              eapply obj_same_id_in_system_same in e; eauto; subst.
              disc_rule_conds.
              eapply rsDown_in_deqMP_false
                with (cobj:= cobj) (rsdm1:= valOf i) (rsdm2:= rsdm); eauto.
            }
            { apply InMP_deqMP in H26; specialize (H3 H26).
              destruct H3; [left; red in H3; red; mred|].
              dest; right; split.
              { red in H3; red; mred.
                destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
                destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
                intros; specialize (H3 _ _ H32 H33 H34).
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

      + apply InMP_enqMP_or in H27; destruct H27.
        * dest; subst; disc_rule_conds.
          eapply obj_same_id_in_system_same in H23; eauto; subst.
          left; red; repeat (simpl; mred).
        * apply InMP_deqMsgs in H6.
          specialize (H3 H6).
          destruct (eq_nat_dec (obj_idx obj) (obj_idx pobj)).
          { eapply obj_same_id_in_system_same in e; eauto; subst.
            left; red; repeat (simpl; mred).
          }
          { destruct H3.
            { left; red; repeat (simpl; mred). }
            { rewrite <-H29 in H31.
              dest; right; split.
              { red in H3; red; mred.
                destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
                destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
                intros; specialize (H3 _ _ H32 H33 H34).
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
            
      + apply InMP_enqMP_or in H27; destruct H27;
          [dest; subst; solve_midx_false|].
        apply InMP_deqMsgs in H22.
        specialize (H3 H22).
        destruct (eq_nat_dec (obj_idx obj) (obj_idx pobj)).
        * eapply obj_same_id_in_system_same in e; eauto; subst.
          left; red; repeat (simpl; mred).
        * destruct H3.
          { left; red; repeat (simpl; mred). }
          { rewrite <-H29 in H7.
            dest; right; split.
            { red in H3; red; mred.
              destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
              destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
              intros; specialize (H3 _ _ H30 H31 H32).
              disc_rule_conds.
              solve_q; assumption.
            }
            { apply FirstMP_enqMP.
              apply FirstMP_deqMsgs; [|eassumption].
              solve_midx_disj.
            }
          }

    - disc_rule_conds.
      apply InMP_enqMsgs_or in H28; destruct H28.
      1:{ exfalso.
          rewrite Forall_forall in H27; specialize (H27 _ H5).
          simpl in H27; rewrite H26 in H27; discriminate.
      }

      destruct (eq_nat_dec (obj_idx obj) (obj_idx pobj)).
      + apply InMP_deqMP in H5.
        specialize (H3 H5).
        eapply obj_same_id_in_system_same in e; eauto; subst.
        right; split.
        * destruct (in_dec eq_nat_dec down (idsOf routs)).
          { red; repeat (simpl; mred).
            intros; solve_q.
            destruct H19.
            apply in_map_iff in i; destruct i as [[down' rqdm] ?]; dest.
            simpl in *; subst.
            erewrite findQ_In_NoDup_enqMsgs; try eassumption.
            rewrite Forall_forall in H27; specialize (H27 _ H36); simpl in H27.
            rewrite filter_app; simpl.
            rewrite H27; simpl.
            destruct (filter _ _); discriminate.
          }
          { red; repeat (simpl; mred).
            intros; disc_rule_conds.
            elim n; clear n.
            eapply RqRsDownMatch_rs_rq in H20; [|eassumption].
            destruct H20 as [cidx [rdown ?]]; dest.
            disc_rule_conds.
          }
        * apply FirstMP_enqMsgs.
          apply FirstMP_deqMP.
          { apply parentIdxOf_not_eq in H24; [|apply Hrrs].
            solve_midx_neq.
          }
          { eapply rsDown_rqsQ_nil_in_first with (cobj:= cobj); eauto.
            good_locking_get pobj.
            red in H30; mred.
            specialize (H30 _ H24).
            destruct H30 as [rdown [rsUp ?]]; dest.
            disc_rule_conds.
            apply H33.
          }

      + destruct (eq_nat_dec (obj_idx obj) (obj_idx cobj)).
        * eapply obj_same_id_in_system_same in e; eauto; subst.
          disc_rule_conds.
          exfalso.
          eapply rsDown_in_deqMP_false
            with (cobj:= cobj) (rsdm1:= rsm) (rsdm2:= rsdm); eauto.
        * apply InMP_deqMP in H5.
          specialize (H3 H5).
          destruct H3; [left; red; mred|].
          dest; right; split.
          { red in H3; red; mred.
            destruct (orqs@[obj_idx pobj]) eqn:Horq; simpl in *; auto.
            destruct (o@[downRq]) eqn:Hrqid; simpl in *; auto.
            intros; specialize (H3 _ _ H30 H32 H33).
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
    destruct Hrrs as [? [? ?]]; red; intros.
    inv H4.
    - assumption.
    - apply noRqRsDown_step_ext_in; auto.
    - apply noRqRsDown_step_ext_out; auto.
    - eapply noRqRsDown_step_int; eauto.
      econstructor; eauto.
  Qed.

  Lemma noRqRsDown_ok:
    InvReachable sys step_m NoRqRsDown.
  Proof.
    apply inv_reachable.
    - apply noRqRsDown_InvInit.
    - apply noRqRsDown_InvStep.
  Qed.

End RqRsDown.

Section Corollaries.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypothesis (Hrrs: RqRsSys dtr sys).

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
            st.(bst_msgs) = msgs ->
            msg_type rsdm = MRs ->
            InMP down rsdm msgs ->
            msg_type rqdm = MRq ->
            ~ FirstMP msgs down rqdm.
  Proof.
    destruct Hrrs as [? [? ?]]; intros; subst.
    pose proof (downLockInv_ok H0 H H2) as Hdlinv.
    pose proof (noRqRsDown_ok Hrrs H2) as Hrrinv.
    red in Hrrinv.
    specialize (Hrrinv _ _ H3 H4 H5 _ H6 _ H8 H9).
    destruct Hrrinv.
    - intro Hx.
      good_locking_get pobj.
      assert (DownLockFreeInv dtr (bst_orqs st) (bst_msgs st) (obj_idx pobj)).
      { red in H7, H11.
        destruct ((bst_orqs st)@[obj_idx pobj]) eqn:Horq; simpl in *.
        { rewrite H7 in H11; assumption. }
        { assumption. }
      }
      clear H11.
      specialize (H12 _ H5); destruct H12 as [rdown [rsUp ?]]; dest.
      repeat disc_rule_minds.
      red in H13; dest.
      apply FirstMP_InMP in Hx.
      apply rqsQ_length_ge_one in Hx; [|assumption].
      rewrite H11 in Hx; simpl in Hx; omega.
    - dest; intro Hx.
      pose proof (FirstMP_eq H11 Hx); subst.
      rewrite H8 in H10; discriminate.
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
            st.(bst_msgs) = msgs ->
            msg_type rqdm = MRq ->
            In rqdm dq ->
            msg_type rsdm = MRs ->
            findQ down msgs = dq ++ [rsdm] ->
            False.
  Proof.
    destruct Hrrs as [? [? ?]]; intros; subst.
    pose proof (upLockInv_ok H0 H H2) as Hulinv.
    pose proof (downLockInv_ok H0 H H2) as Hdlinv.
    pose proof (noRqRsDown_ok Hrrs H2) as Hrrinv.
    assert (InMP down rsdm st.(bst_msgs)).
    { red; rewrite H11.
      apply in_or_app; right; left; reflexivity.
    }
    
    red in Hrrinv.
    specialize (Hrrinv _ _ H3 H4 H5 _ H6 _ H10 H7); clear H7.
    destruct Hrrinv; dest.
    - good_locking_get pobj.
      eapply downLockInvORq_down_rqsQ_length_one_locked in H13; eauto;
        [|eapply rqsQ_length_ge_one; eauto;
          red; rewrite H11; apply in_or_app; left; assumption].
      destruct H13 as [rqid ?]; dest.
      red in H7.
      destruct ((bst_orqs st)@[obj_idx pobj]) eqn:Horq; [simpl in *|discriminate].
      destruct (o@[downRq]) eqn:Hrqid; [simpl in *|discriminate].
      discriminate.
    - good_locking_get cobj.
      eapply upLockInvORq_down_rssQ_length_two_False in H13; eauto.
      unfold rssQ; rewrite H11.
      rewrite filter_app; simpl.
      rewrite H10; simpl.
      rewrite app_length; simpl.
      unfold FirstMP, firstMP in H12.
      rewrite H11 in H12.
      destruct dq as [|dmsg dq]; [elim H9|].
      simpl in H12; inv H12.
      simpl; rewrite H10; simpl.
      omega.
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
            st.(bst_msgs) = msgs ->
            msg_type rsdm = MRs ->
            InMP down rsdm msgs ->
            ~ InMP rsUp rsum msgs.
  Proof.
    destruct Hrrs as [? [? ?]]; intros; subst.
    pose proof (downLockInv_ok H0 H H2) as Hdlinv.
    pose proof (noRqRsDown_ok Hrrs H2) as Hrrinv.
    red in Hrrinv.
    specialize (Hrrinv _ _ H3 H4 H5 _ H6 _ H9 H10).
    destruct Hrrinv.
    - intro Hx.
      good_locking_get pobj.
      assert (DownLockFreeInv dtr (bst_orqs st) (bst_msgs st) (obj_idx pobj)).
      { red in H8, H11.
        destruct ((bst_orqs st)@[obj_idx pobj]) eqn:Horq; simpl in *.
        { rewrite H8 in H11; assumption. }
        { assumption. }
      }
      clear H11.
      specialize (H12 _ H5); destruct H12 as [rdown [rrsUp ?]]; dest.
      repeat disc_rule_minds.
      red in H13; dest.
      apply findQ_length_ge_one in Hx.
      rewrite H12 in Hx; simpl in Hx; omega.
    - dest; intro Hx.
      good_locking_get pobj.
      eapply downLockInvORq_rsUp_length_one_locked in H12; eauto;
        [|eapply findQ_length_ge_one; eassumption].
      destruct H12 as [rqid ?]; dest.
      red in H8.
      destruct ((bst_orqs st)@[obj_idx pobj]) eqn:Horq; [simpl in *|exfalso; auto].
      destruct (o@[downRq]) eqn:Hrqid; [simpl in *|exfalso; auto].
      inv H12.
      specialize (H8 _ _ H6 H7 H14).
      specialize (H13 _ H5); destruct H13 as [rdown [rrsUp ?]]; dest.
      repeat disc_rule_minds.
      destruct (in_dec _ _ _); auto.
      red in H15; dest.
      xor3_contra1 H15.
      + destruct (rqsQ (bst_msgs st) rdown); [exfalso; auto|].
        simpl in *; omega.
      + apply findQ_length_ge_one in Hx.
        omega.
  Qed.

End Corollaries.
      
Close Scope list.
Close Scope fmap.

