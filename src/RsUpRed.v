Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.
Require Import RqRsInvMsg RqRsInvLock RqRsInvAtomic RqUpRed.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section RsUpReduction.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).

  Ltac disc_rule_custom ::=
    try disc_lock_conds;
    try disc_footprints_ok.

  Lemma rsUp_spec:
    forall oidxTo rsUps,
      RsUpMsgs dtr oidxTo rsUps ->
      forall st1 oidx ridx routs st2,
        Reachable (steps step_m) sys st1 ->
        step_m sys st1 (RlblInt oidx ridx rsUps routs) st2 ->
        (* oidxTo = oidx /\ <- requires [rsUps <> nil] <- requires an invariant *)
        (exists obj rule,
            In obj sys.(sys_objs) /\ obj.(obj_idx) = oidx /\
            In rule obj.(obj_rules) /\ rule.(rule_idx) = ridx /\
            RsUp rule /\ RsBackRuleCommon rule) /\
        (exists oorq orqid,
            st1.(bst_orqs)@[oidx] = Some oorq /\
            oorq@[downRq] = Some orqid /\
            DownLockedInv dtr st1.(bst_orqs) st1.(bst_msgs) oidx orqid).
  Proof.
    intros; destruct Hrrs as [? [? ?]].

    pose proof (footprints_ok H3 H0).
    pose proof (downLockInv_ok H3 H2 H0).

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
        exfalso; destruct H31 as [ncidx [? ?]].
        elim (rqrsDTree_rsUp_down_not_eq H2 _ _ H23 H14); reflexivity.
      + split.
        * exists obj, rule.
          repeat ssplit; try assumption; try reflexivity.
        * disc_rule_conds.
          { exists porq, rqi.
            repeat ssplit; try assumption; try reflexivity.
            red in H10; rewrite H30 in H10; assumption.
          }
          { exists porq, rqi.
            repeat ssplit; try assumption; try reflexivity.
            red in H10; rewrite H30 in H10; assumption.
          }

    - exfalso; disc_rule_conds.
      destruct H26 as [cidx ?]; dest.
      elim (rqrsDTree_rsUp_down_not_eq H2 _ _ H7 H34); reflexivity.
  Qed.

  Lemma rsUp_not_down_requested:
    forall orqs msgs oidx porq rqi rqDowns rsUps P,
      DownLockedInv dtr (orqs +[oidx <- porq +[downRq <- rqi]])
                    (enqMsgs rqDowns msgs) oidx rqi ->
      rqDowns <> nil -> NoDup (idsOf rqDowns) ->
      Forall (fun idm => msg_type (valOf idm) = MRq) rqDowns ->
      Forall (FirstMPI (enqMsgs rqDowns msgs)) rsUps ->
      idsOf rsUps = rqi_minds_rss rqi ->
      RqRsDownMatch dtr oidx (idsOf rqDowns) (idsOf rsUps) P ->
      False.
  Proof.
    intros.
    assert (exists rqTo, In rqTo (idsOf rqDowns)).
    { destruct rqDowns as [|[rqDown rqm] ?]; [exfalso; auto|].
      eexists; left; reflexivity.
    }
    destruct H6 as [rqTo ?]; dest.
    pose proof (RqRsDownMatch_rq_rs H5 _ H6).
    destruct H7 as [cidx [rsUp ?]]; dest; simpl in *.
    
    specialize (H _ H7).
    destruct H as [down [rrsUp ?]]; dest.
    repeat disc_rule_minds.
    destruct (in_dec eq_nat_dec rsUp (rqi_minds_rss rqi));
      [|elim n; rewrite <-H4; assumption].

    red in H12; dest.
    xor3_contra1 H12.
    { assert_later (length (rqsQ (enqMsgs rqDowns msgs) rqTo) >= 1); [omega|].
      apply in_map_iff in H6.
      destruct H6 as [[rqDown rqm] ?]; dest; simpl in *; subst.
      rewrite Forall_forall in H2; specialize (H2 _ H13); simpl in *.
      unfold rqsQ.
      erewrite findQ_In_NoDup_enqMsgs; eauto.
      rewrite filter_app; simpl.
      rewrite H2; simpl.
      rewrite app_length; simpl; omega.
    }
    { apply in_map_iff in H10.
      destruct H10 as [[rrsUp rsm] ?]; dest; simpl in *; subst.
      rewrite Forall_forall in H3; specialize (H3 _ H13); simpl in *.
      eapply findQ_length_one; eauto.
    }
  Qed.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_msgs_in;
    try disc_rqToUpRule.

  Ltac solve_midx_disj :=
    repeat
      match goal with
      | [ |- _ <> _] => solve_midx_neq
      | [ |- ~ In _ _] => solve_midx_neq
      | [ |- DisjList (_ :: nil) (_ :: nil)] =>
        apply (DisjList_singletons eq_nat_dec)
      | [ |- DisjList (_ :: nil) _] =>
        apply (DisjList_singleton_1 eq_nat_dec)
      | [ |- DisjList _ (_ :: nil)] =>
        apply (DisjList_singleton_2 eq_nat_dec)
      end.

  Lemma rsUp_lbl_reducible:
    forall oidxTo rsUps,
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
    pose proof (footprints_ok H2 H4) as HftInv.
    
    pose proof (rsUp_spec H H5 H11).
    destruct H6 as [[obj [rule ?]] [orq [rqid ?]]]; dest.

    pose proof H11; phide H17.
    pose proof H12; phide H17.
    inv_step; simpl in *.
    red_obj_rule.
    
    good_rqrs_rule_get rule.
    good_rqrs_rule_get rule0.

    destruct (eq_nat_dec (obj_idx obj0) (obj_idx obj1)).
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
          destruct H10 as [rqOIdxTo ?].
          eapply rqUp_lbl_commutes; try eassumption.
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
      
      + rewrite <-H45 in H21.
        good_rqrs_rule_cases rule0.
        * disc_rule_conds.
          destruct (eq_nat_dec cidx (obj_idx upCObj));
            [subst; rewrite H58 in H15; elim n; inv H15; reflexivity|].
          split; [|split]; [|assumption|]; solve_midx_disj.
        * disc_rule_conds.
          split; [|split]; [|assumption|]; solve_midx_disj.
        * assert (Some (obj_idx obj1) <> Some (obj_idx obj0))
            by (intro Hx; inv Hx; auto).
          disc_rule_conds.
          { split; [|split]; [|assumption|]; solve_midx_disj. }
          { split; [|split]; [|assumption|]; solve_midx_disj. }
          { split; [|split]; [|assumption|]; solve_midx_disj. }
        * good_footprint_get (obj_idx obj0).
          disc_rule_conds.
          { destruct (eq_nat_dec cidx (obj_idx upCObj));
              [subst; rewrite H14 in H15; elim n; inv H15; reflexivity|].
            split; [|split]; [|assumption|]; solve_midx_disj.
          }
          { split; [|split]; [|assumption|].
            { rewrite H54; eapply RqRsDownMatch_rss_disj; eauto. }
            { destruct (eq_nat_dec (obj_idx upCObj0) (obj_idx upCObj));
              [rewrite e in *; rewrite H39 in H15; elim n; inv H15; reflexivity|].
              solve_midx_disj.
            }
          }
          { split; [|split]; [|assumption|].
            { rewrite H54; eapply RqRsDownMatch_rss_disj; eauto. }
            { solve_midx_disj. }
          }
        * assert (Some (obj_idx obj1) <> Some (obj_idx obj0))
            by (intro Hx; inv Hx; auto).
          disc_rule_conds.
          split; [|split]; [|assumption|]; solve_midx_disj.

      + rewrite <-H45 in H15.
        good_rqrs_rule_cases rule0.
        * disc_rule_conds.
          split; [|split]; [|assumption|]; solve_midx_disj.
        * disc_rule_conds.
          split; [|split]; [|assumption|]; solve_midx_disj.
        * disc_rule_conds.
          { split; [|split]; [|assumption|]; solve_midx_disj. }
          { split; [|split]; [|assumption|]; solve_midx_disj. }
          { split; [|split]; [|assumption|]; solve_midx_disj. }
        * good_footprint_get (obj_idx obj0).
          disc_rule_conds.
          { split; [|split]; [|assumption|]; solve_midx_disj. }
          { split; [|split]; [|assumption|].
            { rewrite H52; eapply RqRsDownMatch_rss_disj; eauto. }
            { solve_midx_disj. }
          }
          { split; [|split]; [|assumption|].
            { rewrite H52; eapply RqRsDownMatch_rss_disj; eauto. }
            { solve_midx_disj. }
          }
        * disc_rule_conds.
          split; [|split]; [|assumption|]; solve_midx_disj.
  Qed.

  Lemma rsUp_lbl_rins_ids_disj:
    forall objTo rsUps,
      In objTo (sys_objs sys) ->
      RsUpMsgs dtr objTo.(obj_idx) rsUps ->
      forall oidx ridx rins routs,
        NoDup (idsOf routs) ->
        DisjList rsUps rins ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(bst_msgs)) rsUps ->
          step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
          DisjList (idsOf rsUps) (idsOf rins).
  Proof.
  Admitted.

  Lemma rsUp_lbl_outs_disj:
    forall objTo rsUps,
      In objTo (sys_objs sys) ->
      RsUpMsgs dtr objTo.(obj_idx) rsUps ->
      forall oidx ridx rins routs,
        NoDup (idsOf routs) ->
        DisjList rsUps rins ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(bst_msgs)) rsUps ->
          step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
          DisjList routs rsUps.
  Proof.
    destruct Hrrs as [? [? ?]].
    intros.
    eapply rsUp_lbl_rins_ids_disj in H5; eauto.

    assert (Reachable (steps step_m) sys st2).
    { eapply reachable_steps; [eassumption|].
      apply steps_singleton; eassumption.
    }

    inv_step; simpl in *.
    pose proof (downLockInv_ok H0 H H9).
    good_locking_get objTo; clear H8.
    red in H10.

    red; intro rsUp.
    destruct (in_dec (id_dec msg_dec) rsUp routs) as [Hin1|]; auto.
    destruct (in_dec (id_dec msg_dec) rsUp rsUps) as [Hin2|]; auto.
    exfalso.
    destruct rsUp as [rsUp rsm].
    pose proof (in_map idOf _ _ Hin2); simpl in *.
    red in H3; dest.
    rewrite Forall_forall in H11; specialize (H11 _ H8).
    destruct H11 as [cidx [? ?]].
    
    assert (length (findQ rsUp (enqMsgs routs (deqMsgs (idsOf rins) msgs))) >= 2).
    { erewrite findQ_In_NoDup_enqMsgs by eassumption.
      rewrite app_length; simpl.
      rewrite findQ_not_In_deqMsgs.
      { rewrite Forall_forall in H7.
        specialize (H7 _ Hin2).
        remember (findQ rsUp msgs) as q; destruct q.
        { exfalso; eapply InMP_findQ_False; eauto. }
        { simpl; omega. }
      }
      { destruct (H5 rsUp); auto. }
    }

    destruct (((orqs +[obj_idx obj <- norq])@[obj_idx objTo])
                >>=[[]] (fun orq => orq)@[downRq]).
    + specialize (H10 _ H11).
      destruct H10 as [down [rrsUp ?]]; dest.
      repeat disc_rule_minds.
      find_if_inside.
      * red in H23; dest; omega.
      * red in H23; dest.
        rewrite H23 in H13; simpl in H13; omega.
    + specialize (H10 _ H11).
      destruct H10 as [down [rrsUp ?]]; dest.
      repeat disc_rule_minds.
      red in H23; dest.
      rewrite H23 in H13; simpl in H13; omega.
  Qed.
  
  Lemma rsUp_atomic_outs_disj:
    forall objTo rsUps,
      In objTo (sys_objs sys) ->
      RsUpMsgs dtr objTo.(obj_idx) rsUps ->
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
    induction 3; simpl; intros; subst.
    - inv_steps.
      eapply rsUp_lbl_outs_disj; eauto.
      inv_step; destruct H22; assumption.
    - inv H13.
      apply DisjList_app_4; eauto.
      eapply rsUp_lbl_outs_disj.
      { eassumption. }
      { assumption. }
      { inv_step; destruct H26; assumption. }
      { instantiate (1:= rins).
        specialize (IHAtomic H10 _ _ H11 H12 H14).
        eapply DisjList_comm, DisjList_SubList; [eassumption|].
        eapply DisjList_SubList; [|eassumption].
        eapply atomic_eouts_in; eauto.
      }
      { eapply reachable_steps; eassumption. }
      { rewrite Forall_forall in H12.
        apply Forall_forall; intros rsUp ?.
        specialize (H12 _ H7).
        eapply (atomic_messages_in_in msg_dec); eauto.
        specialize (H10 rsUp); destruct H10; auto.
      }
      { eassumption. }
  Qed.

  Lemma rsUp_rpush_unit_ok_ind':
    forall oidxTo rsUps inits ins hst outs eouts
           oidx ridx routs,
      RsUpMsgs dtr oidxTo rsUps ->
      Atomic msg_dec inits ins hst outs eouts ->
      DisjList outs rsUps ->
      Reducible sys (RlblInt oidx ridx rsUps routs :: hst)
                (hst ++ [RlblInt oidx ridx rsUps routs]).
  Proof.
    induction 2; simpl; intros; subst.
    - eapply rsUp_lbl_reducible; eauto.
    - apply DisjList_app_3 in H6; dest.
      eapply reducible_trans.
      + apply reducible_cons_2.
        eapply rsUp_lbl_reducible; eauto.
      + apply reducible_cons; eauto.
  Qed.

  Lemma rsUp_rpush_unit_ok_ind:
    forall oidxTo rsUps inits ins hst outs eouts
           oidx ridx routs,
      RsUpMsgs dtr oidxTo rsUps ->
      Atomic msg_dec inits ins hst outs eouts ->
      DisjList rsUps inits ->
      Reducible sys (RlblInt oidx ridx rsUps routs :: hst)
                (hst ++ [RlblInt oidx ridx rsUps routs]).
  Proof.
    intros.
    pose proof H0.
    red; intros.
    eapply rsUp_rpush_unit_ok_ind'; eauto.
    inv H3.

    (* pose proof (rsUp_spec H (reachable_steps Hr H7) H9). *)
    eapply rsUp_atomic_outs_disj; eauto.
  Admitted.
  
End RsUpReduction.

Close Scope list.
Close Scope fmap.

