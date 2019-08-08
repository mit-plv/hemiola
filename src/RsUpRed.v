Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.
Require Import RqRsInvMsg RqRsInvLock RqUpRed.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section RsUpReduction.
  Context `{oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System).

  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hrrs: RqRsSys dtr sys).

  Ltac disc_rule_custom ::=
    try disc_lock_conds;
    try disc_footprints_ok.

  Lemma rsUp_spec:
    forall oidxTo rsUps (HrsUps: rsUps <> nil),
      RsUpMsgs dtr oidxTo rsUps ->
      forall st1 oidx ridx routs st2,
        Reachable (steps step_m) sys st1 ->
        step_m sys st1 (RlblInt oidx ridx rsUps routs) st2 ->
        (oidxTo = oidx /\
         Forall (fun rsUp =>
                   exists cidx,
                     parentIdxOf dtr cidx = Some oidx /\
                     rsEdgeUpFrom dtr cidx = Some (idOf rsUp)) rsUps) /\
        (exists obj rule,
            In obj sys.(sys_objs) /\ obj.(obj_idx) = oidx /\
            In rule obj.(obj_rules) /\ rule.(rule_idx) = ridx /\
            RsUp rule /\ RsBackRuleCommon rule) /\
        (exists oorq orqid,
            st1.(bst_orqs)@[oidx] = Some oorq /\
            oorq@[downRq] = Some orqid /\
            DownLockedInv dtr st1.(bst_orqs) st1.(bst_msgs) oidx orqid).
  Proof.
    intros; destruct Hrrs as [? [? [_ ?]]].
    pose proof (footprints_ok Hiorqs H3 H0).
    pose proof (downLockInv_ok Hiorqs H3 H2 H4 H0).
    red in H; dest.
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - exfalso; disc_rule_conds.
    - exfalso; disc_rule_conds.
    - exfalso; disc_rule_conds.

    - good_footprint_get (obj_idx obj).
      good_locking_get obj.
      red in H1; dest; destruct H1.
      + disc_rule_conds.
        * solve_midx_false.
        * exfalso.
          elim (rqrsDTree_rsUp_down_not_eq H2 _ _ H17 H8); reflexivity.
      + split.
        { disc_rule_conds.
          { split.
            { rewrite <-H33 in H29.
              assert (exists rsUp, In rsUp (idsOf rsUps)).
              { apply RqRsDownMatch_rs_not_nil in H29.
                destruct (idsOf rsUps); [exfalso; auto|].
                eexists; left; reflexivity.
              }
              destruct H14 as [rsUp ?].
              rewrite Forall_forall in H7; specialize (H7 _ H14).
              destruct H7 as [cidx ?]; dest.
              eapply RqRsDownMatch_rs_rq in H29; [|eassumption].
              destruct H29 as [rcidx [down ?]]; dest.
              repeat disc_rule_minds.
              reflexivity.
            }
            { rewrite <-H33 in H29.
              apply Forall_forall; intros rsUp ?.
              apply in_map with (f:= idOf) in H14.
              eapply RqRsDownMatch_rs_rq in H29; [|eassumption].
              destruct H29 as [cidx [down ?]]; dest; eauto.
            }
          }
          { split.
            { rewrite <-H33 in H21.
              assert (exists rsUp, In rsUp (idsOf rsUps)).
              { apply RqRsDownMatch_rs_not_nil in H21.
                destruct (idsOf rsUps); [exfalso; auto|].
                eexists; left; reflexivity.
              }
              destruct H26 as [rsUp ?].
              rewrite Forall_forall in H7; specialize (H7 _ H26).
              destruct H7 as [cidx ?]; dest.
              eapply RqRsDownMatch_rs_rq in H21; [|eassumption].
              destruct H21 as [rcidx [down ?]]; dest.
              repeat disc_rule_minds.
              reflexivity.
            }
            { rewrite <-H33 in H21.
              apply Forall_forall; intros rsUp ?.
              apply in_map with (f:= idOf) in H26.
              eapply RqRsDownMatch_rs_rq in H21; [|eassumption].
              destruct H21 as [cidx [down ?]]; dest; eauto.
            }
          }
        }
        { split.
          { exists obj, rule.
            repeat ssplit; try assumption; try reflexivity.
          }
          { disc_rule_conds.
            { exists porq, rqi.
              repeat ssplit; try assumption; try reflexivity.
            }
            { exists porq, rqi.
              repeat ssplit; try assumption; try reflexivity.
            }
          }
        }
          
    - good_footprint_get (obj_idx obj).
      exfalso; disc_rule_conds.
      solve_midx_false.
  Qed.

  Lemma rsUp_not_down_requested:
    forall orqs msgs oidx porq rqi rqDowns rsUps P,
      DownLockedInv dtr (orqs +[oidx <- porq +[downRq <- rqi]])
                    (enqMsgs rqDowns msgs) oidx rqi ->
      NoDup (idsOf rqDowns) ->
      Forall (fun idm => msg_type (valOf idm) = MRq) rqDowns ->
      Forall (FirstMPI (enqMsgs rqDowns msgs)) rsUps ->
      idsOf rsUps = rqi_minds_rss rqi ->
      RqRsDownMatch dtr oidx (idsOf rqDowns) (idsOf rsUps) P ->
      False.
  Proof.
    intros.
    assert (exists rqTo, In rqTo (idsOf rqDowns)).
    { destruct rqDowns as [|[rqDown rqm] ?].
      { red in H4; dest; elim H4; reflexivity. }
      { eexists; left; reflexivity. }
    }
    destruct H5 as [rqTo ?]; dest.
    pose proof (RqRsDownMatch_rq_rs H4 _ H5).
    destruct H6 as [cidx [rsUp ?]]; dest; simpl in *.
    
    specialize (H _ H7).
    destruct H as [down [rrsUp ?]]; dest.
    repeat disc_rule_minds.
    destruct (in_dec idx_dec rsUp (rqi_minds_rss rqi));
      [|elim n; rewrite <-H3; assumption].

    red in H12; dest.
    xor3_contra1 H12.
    { assert_later (length (rqsQ (enqMsgs rqDowns msgs) rqTo) >= 1); [omega|].
      apply in_map_iff in H5.
      destruct H5 as [[rqDown rqm] ?]; dest; simpl in *; subst.
      rewrite Forall_forall in H1; specialize (H1 _ H13); simpl in *.
      unfold rqsQ.
      erewrite findQ_In_NoDup_enqMsgs; eauto.
      rewrite filter_app; simpl.
      rewrite H1; simpl.
      rewrite app_length; simpl; omega.
    }
    { apply in_map_iff in H10.
      destruct H10 as [[rrsUp rsm] ?]; dest; simpl in *; subst.
      rewrite Forall_forall in H2; specialize (H2 _ H13); simpl in *.
      eapply findQ_length_one; eauto.
    }
  Qed.

  Ltac disc_rqUpMsgs :=
    match goal with
    | [H: RqUpMsgs _ _ _ |- _] =>
      let cidx := fresh "cidx" in
      let rqUp := fresh "rqUp" in
      destruct H as [cidx [rqUp ?]]; dest
    end.
  
  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_rqUpMsgs;
    try disc_rqToUpRule.

  Lemma rsUp_lbl_reducible:
    forall oidxTo rsUps (HrsUps: rsUps <> nil),
      RsUpMsgs dtr oidxTo rsUps ->
      forall oidx1 ridx1 rins1 routs1 oidx2 ridx2 routs2,
        DisjList routs1 rsUps ->
        Reducible
          sys [RlblInt oidx2 ridx2 rsUps routs2;
                 RlblInt oidx1 ridx1 rins1 routs1]
          [RlblInt oidx1 ridx1 rins1 routs1;
             RlblInt oidx2 ridx2 rsUps routs2].
  Proof.
    intros.
    destruct Hrrs as [? [? ?]].
    apply internal_steps_commutes; intros.

    (* Register necessary invariants. *)
    inv_steps.
    assert (Reachable (steps step_m) sys st3).
    { eapply reachable_steps; [eassumption|].
      econstructor; [econstructor|eassumption].
    }
    pose proof (footprints_ok Hiorqs H2 H4) as HftInv.

    pose proof (rsUp_spec HrsUps H H5 H11).
    destruct H6 as [_ [[obj [rule ?]] [orq [rqid ?]]]]; dest.

    pose proof H11; phide H17.
    pose proof H12; phide H17.
    inv_step; simpl in *.
    red_obj_rule.
    
    good_rqrs_rule_get rule.
    good_rqrs_rule_get rule0.

    destruct (idx_dec (obj_idx obj0) (obj_idx obj1)).
    - red_obj_rule; mred.
      good_rqrs_rule_cases rule0.
      + (** case [ImmDownRule] *)
        disc_rule_conds.
      + (** case [ImmUpRule] *)
        disc_rule_conds.
      + (** case [RqFwdRule] *)
        destruct H7; destruct H10 as [|[|]].
        * (** [RqUpUp]; already proven in [RqUpRed.v]! *)
          preveal H18; preveal H19.
          (* This reachability below confuses [eauto] 
           * to prove the goal automatically. *)
          clear H5.
          eapply rqUpUp_rqUpMsgs with (routs:= routs1) in H10;
            try eassumption; try reflexivity.
          destruct H10 as [? [rqOIdxTo ?]].
          eapply rqUp_lbl_commutes with (rqUps:= routs1); try eassumption.
          { apply SubList_refl. }
          { econstructor.
            { econstructor; [econstructor|eassumption]. }
            { eassumption. }
          }
        * (** [RqUpDown] *)
          exfalso; phide_clear.
          disc_rule_conds.
          destruct H33.
          rewrite <-H59 in H21.
          eapply rsUp_not_down_requested; eauto.
        * (** [RqDownDown] *)
          exfalso; phide_clear.
          disc_rule_conds.
          destruct H33.
          rewrite <-H59 in H12.
          eapply rsUp_not_down_requested; eauto.

      + (** case [RsBackRule] *)
        disc_rule_conds.

      + (** case [RsDownRqDownRule] *)
        exfalso; phide_clear.
        disc_rule_conds.
        destruct H33.
        rewrite <-H54 in H18.
        eapply rsUp_not_down_requested; eauto.

    - phide_clear.
      split; [red; auto|].
      good_footprint_get (obj_idx obj1).
      disc_rule_conds.
      
      + rewrite <-H45 in H22.
        good_rqrs_rule_cases rule0.
        * disc_rule_conds; [repeat split; apply DisjList_nil_1|].
          destruct (idx_dec cidx (obj_idx upCObj));
            [subst; rewrite H59 in H17; elim n; inv H17; reflexivity|].
          split; [|split]; [|assumption|]; solve_midx_disj.
        * disc_rule_conds.
          split; [|split]; [|assumption|]; solve_midx_disj.
        * assert (Some (obj_idx obj1) <> Some (obj_idx obj0))
            by (intro Hx; inv Hx; auto).
          disc_rule_conds.
          { split; [|split]; [apply DisjList_nil_1|assumption|solve_midx_disj]. } 
          { split; [|split]; [|assumption|]; solve_midx_disj. }
          { split; [|split]; [|assumption|]; solve_midx_disj. }
          { split; [|split]; [|assumption|]; solve_midx_disj. }
        * good_footprint_get (obj_idx obj0).
          disc_rule_conds.
          { destruct (idx_dec cidx (obj_idx upCObj));
              [subst; rewrite H15 in H17; elim n; inv H17; reflexivity|].
            split; [|split]; [|assumption|]; solve_midx_disj.
          }
          { split; [|split];
              [solve_midx_disj|apply DisjList_nil_1|apply DisjList_nil_1].
          }
          { split; [|split]; [|assumption|].
            { rewrite H55; eapply RqRsDownMatch_rss_disj; eauto. }
            { destruct (idx_dec (obj_idx upCObj0) (obj_idx upCObj));
                [rewrite e in *; rewrite H43 in H17; elim n; inv H17; reflexivity|].
              solve_midx_disj.
            }
          }
          { split; [|split]; [|assumption|].
            { rewrite H55; eapply RqRsDownMatch_rss_disj; eauto. }
            { solve_midx_disj. }
          }
        * good_footprint_get (obj_idx obj0).
          disc_rule_conds.
          assert (Some (obj_idx obj1) <> Some (obj_idx obj0))
            by (intro Hx; inv Hx; auto).
          split; [|split]; [|assumption|]; solve_midx_disj.

      + rewrite <-H45 in H17.
        good_rqrs_rule_cases rule0.
        * disc_rule_conds.
          { split; [|split]; apply DisjList_nil_1. }
          { split; [|split]; [|assumption|]; solve_midx_disj. }
        * disc_rule_conds.
          split; [|split]; [|assumption|]; solve_midx_disj.
        * disc_rule_conds.
          { split; [|split]; [apply DisjList_nil_1|assumption|solve_midx_disj]. }
          { split; [|split]; [|assumption|]; solve_midx_disj. }
          { split; [|split]; [|assumption|]; solve_midx_disj. }
          { split; [|split]; [|assumption|]; solve_midx_disj. }
        * good_footprint_get (obj_idx obj0).
          disc_rule_conds.
          { split; [|split]; [|assumption|]; solve_midx_disj. }
          { split; [|split]; [solve_midx_disj|assumption|apply DisjList_nil_1]. }
          { split; [|split]; [|assumption|].
            { rewrite H53; eapply RqRsDownMatch_rss_disj; eauto. }
            { solve_midx_disj. }
          }
          { split; [|split]; [|assumption|].
            { rewrite H53; eapply RqRsDownMatch_rss_disj; eauto. }
            { solve_midx_disj. }
          }
        * good_footprint_get (obj_idx obj0).
          disc_rule_conds.
          split; [|split]; [|assumption|]; solve_midx_disj.
  Qed.

  Lemma rsUp_lbl_rins_ids_disj:
    forall objTo rsUps,
      In objTo (sys_objs sys) ->
      RsUpMsgs dtr objTo.(obj_idx) rsUps ->
      Forall (fun rsUp =>
                exists cidx,
                  parentIdxOf dtr cidx = Some objTo.(obj_idx) /\
                  rsEdgeUpFrom dtr cidx = Some (idOf rsUp)) rsUps ->
      forall oidx ridx rins routs,
        NoDup (idsOf routs) ->
        DisjList rsUps rins ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(bst_msgs)) rsUps ->
          step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
          DisjList (idsOf rsUps) (idsOf rins).
  Proof.
    destruct Hrrs as [? [? [_ ?]]]; intros.
    pose proof (downLockInv_ok Hiorqs H0 H H1 H7).
    good_locking_get objTo; clear H10.

    apply (DisjList_false_spec idx_dec); intros rsUp Hin1 Hin2.
    apply in_map_iff in Hin1; destruct Hin1 as [[rsUp' rsm1] ?]; dest; subst.
    apply in_map_iff in Hin2; destruct Hin2 as [[rsUp rsm2] ?]; dest; subst.
    simpl in H10; subst rsUp'.
    destruct (msg_dec rsm1 rsm2); subst;
      [specialize (H6 (rsUp, rsm2)); destruct H6; auto|].

    assert (length (findQ rsUp st1.(bst_msgs)) >= 2).
    { rewrite Forall_forall in H8; specialize (H8 _ H12).
      assert (InMPI (bst_msgs st1) (rsUp, rsm2)).
      { inv_step; simpl.
        apply FirstMPI_Forall_InMP in H22.
        rewrite Forall_forall in H22; auto.
      }
      clear -H8 H10 n.
      unfold InMPI, InMP in *; simpl in *.
      destruct (findQ rsUp (bst_msgs st1)); [elim H8|].
      destruct q; [dest_in; exfalso; auto|].
      simpl; omega.
    }

    rewrite Forall_forall in H4; specialize (H4 _ H12).
    destruct H4 as [cidx [? ?]]; simpl in *.
    eapply downLockInvORq_rsUp_length_two_False; eassumption.
  Qed.

  Lemma rsUp_lbl_outs_disj:
    forall objTo rsUps,
      In objTo (sys_objs sys) ->
      RsUpMsgs dtr objTo.(obj_idx) rsUps ->
      Forall (fun rsUp =>
                exists cidx,
                  parentIdxOf dtr cidx = Some objTo.(obj_idx) /\
                  rsEdgeUpFrom dtr cidx = Some (idOf rsUp)) rsUps ->
      forall oidx ridx rins routs,
        NoDup (idsOf routs) ->
        DisjList rsUps rins ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(bst_msgs)) rsUps ->
          step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
          DisjList routs rsUps.
  Proof.
    destruct Hrrs as [? [? [_ ?]]].
    intros.
    eapply rsUp_lbl_rins_ids_disj in H5; eauto; clear H4.

    assert (Reachable (steps step_m) sys st2).
    { eapply reachable_steps; [eassumption|].
      apply steps_singleton; eassumption.
    }

    inv_step; simpl in *.
    pose proof (downLockInv_ok Hiorqs H0 H H1 H4).
    good_locking_get objTo; clear H9.
    
    apply (DisjList_false_spec (id_dec msg_dec)); intros rsUp Hin1 Hin2.
    destruct rsUp as [rsUp rsm].
    pose proof (in_map idOf _ _ Hin2); simpl in *.
    red in H3; dest.
    rewrite Forall_forall in H11; specialize (H11 _ H9).
    destruct H11 as [cidx [? ?]].

    assert (length (findQ rsUp (enqMsgs routs (deqMsgs (idsOf rins) msgs))) >= 2).
    { destruct H24.
      erewrite findQ_In_NoDup_enqMsgs by eassumption.
      rewrite app_length; simpl.
      rewrite findQ_not_In_deqMsgs.
      { rewrite Forall_forall in H8.
        specialize (H8 _ Hin2).
        remember (findQ rsUp msgs) as q; destruct q.
        { exfalso; eapply InMP_findQ_False; eauto. }
        { simpl; omega. }
      }
      { destruct (H5 rsUp); auto. }
    }

    eapply downLockInvORq_rsUp_length_two_False; eassumption.
  Qed.
  
  Lemma rsUp_atomic_outs_disj:
    forall objTo rsUps,
      In objTo (sys_objs sys) ->
      RsUpMsgs dtr objTo.(obj_idx) rsUps ->
      Forall (fun rsUp =>
                exists cidx,
                  parentIdxOf dtr cidx = Some objTo.(obj_idx) /\
                  rsEdgeUpFrom dtr cidx = Some (idOf rsUp)) rsUps ->
      forall inits ins hst outs eouts,
        Atomic msg_dec inits ins hst outs eouts ->
        DisjList rsUps inits ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(bst_msgs)) rsUps ->
          steps step_m sys st1 hst st2 ->
          DisjList outs rsUps.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 4; simpl; intros; subst.
    - inv_steps.
      eapply rsUp_lbl_outs_disj; eauto.
      inv_step; destruct H23; assumption.
    - inv H14.
      apply DisjList_app_4; eauto.
      eapply rsUp_lbl_outs_disj.
      { eassumption. }
      { assumption. }
      { assumption. }
      { inv_step; destruct H27; assumption. }
      { instantiate (1:= rins).
        specialize (IHAtomic H11 _ _ H12 H13 H15).
        eapply DisjList_comm, DisjList_SubList; [eassumption|].
        eapply DisjList_SubList; [|eassumption].
        eapply atomic_eouts_in; eauto.
      }
      { eapply reachable_steps; eassumption. }
      { rewrite Forall_forall in H13.
        apply Forall_forall; intros rsUp ?.
        specialize (H13 _ H8).
        eapply atomic_messages_in_in; eauto.
        specialize (H11 rsUp); destruct H11; auto.
      }
      { eassumption. }
  Qed.

  Lemma rsUp_rpush_unit_reducible':
    forall oidxTo rsUps (HrsUps: rsUps <> nil)
           inits ins hst outs eouts oidx ridx routs,
      RsUpMsgs dtr oidxTo rsUps ->
      Forall (fun rsUp =>
                exists cidx,
                  parentIdxOf dtr cidx = Some oidxTo /\
                  rsEdgeUpFrom dtr cidx = Some (idOf rsUp)) rsUps ->
      Atomic msg_dec inits ins hst outs eouts ->
      DisjList outs rsUps ->
      Reducible sys (RlblInt oidx ridx rsUps routs :: hst)
                (hst ++ [RlblInt oidx ridx rsUps routs]).
  Proof.
    induction 4; simpl; intros; subst.
    - eapply rsUp_lbl_reducible; eauto.
    - apply DisjList_app_3 in H7; dest.
      eapply reducible_trans.
      + apply reducible_cons_2.
        eapply rsUp_lbl_reducible; eauto.
      + apply reducible_cons; eauto.
  Qed.

  Lemma rsUp_rpush_unit_reducible:
    forall oidxTo rsUps (HrsUps: rsUps <> nil)
           inits ins hst outs eouts oidx ridx routs,
      RsUpMsgs dtr oidxTo rsUps ->
      Atomic msg_dec inits ins hst outs eouts ->
      DisjList rsUps inits ->
      ReducibleP
        sys (fun st => Forall (InMPI st.(bst_msgs)) rsUps)
        (RlblInt oidx ridx rsUps routs :: hst)
        (hst ++ [RlblInt oidx ridx rsUps routs]).
  Proof.
    intros.
    pose proof H0.
    red; intros.
    inv_steps.
    pose proof (rsUp_spec HrsUps H (reachable_steps Hr H7) H9).
    destruct H3 as [[? ?] _]; subst.
    eapply rsUp_rpush_unit_reducible'; eauto.
    - inv_step.
      eapply rsUp_atomic_outs_disj; eauto.
    - econstructor; eauto.
  Qed.

End RsUpReduction.

Close Scope list.
Close Scope fmap.

