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

    - good_locking_get obj.
      red in H1; dest; destruct H1.
      + disc_rule_conds.
        exfalso; destruct H30 as [ncidx [? ?]].
        elim (rqrsDTree_rsUp_down_not_eq H2 _ _ H23 H16); reflexivity.
      + split.
        * exists obj, rule.
          repeat ssplit; try assumption; try reflexivity.
        * disc_rule_conds.
          { exists porq, rqi.
            repeat ssplit; try assumption; try reflexivity.
            red in H8; rewrite H28 in H8; assumption.
          }
          { exists porq, rqi.
            repeat ssplit; try assumption; try reflexivity.
            red in H8; rewrite H28 in H8; assumption.
          }

    - exfalso; disc_rule_conds.
      elim (rqrsDTree_rsUp_down_not_eq H2 _ _ H8 H34); reflexivity.
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

  Lemma rsUp_lbl_reducible:
    forall oidxTo rsUps,
      RsUpMsgs dtr oidxTo rsUps ->
      forall oidx1 ridx1 rins1 routs1 oidx2 ridx2 routs2,
        (* DisjList rsUps rins1 -> *)
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
    pose proof (footprints_ok H2 H5) as HftInv.
    
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
          rewrite <-H59 in H19.
          eapply rsUp_not_down_requested; eauto.
        * (** [RqDownDown] *)
          exfalso; phide_clear.
          disc_rule_conds.
          destruct H33.
          rewrite <-H59 in H10.
          eapply rsUp_not_down_requested; eauto.

      + (** case [RsBackRule] *)
        disc_rule_conds.

      + (** case [RsDownRqDownRule] *)
        exfalso; phide_clear.
        disc_rule_conds.
        destruct H33.
        rewrite <-H54 in H17.
        eapply rsUp_not_down_requested; eauto.

    - split; [red; auto|].
      (* good_footprint_get (obj_idx obj1). *)
      (* disc_rule_conds. *)
    
  Admitted.

  Lemma rsUp_rpush_unit_ok_ind:
    forall oidxTo rsUps inits ins hst outs eouts
           oidx ridx routs,
      RsUpMsgs dtr oidxTo rsUps ->
      Atomic msg_dec inits ins hst outs eouts ->
      DisjList rsUps inits ->
      Reducible sys (RlblInt oidx ridx rsUps routs :: hst)
                (hst ++ [RlblInt oidx ridx rsUps routs]).
  Proof.
    induction 2; simpl; intros; subst.
    - eapply rsUp_lbl_reducible; eauto.
      admit.
    - eapply reducible_trans.
      + apply reducible_cons_2.
        eapply rsUp_lbl_reducible.
        * eassumption.
        * admit.
      + apply reducible_cons; auto.
  Admitted.
  
End RsUpReduction.

Close Scope list.
Close Scope fmap.

