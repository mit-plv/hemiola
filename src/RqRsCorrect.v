Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.
Require Import RqRsInvMsg RqRsInvLock RqRsInvAtomic.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

(** TODO: add more conditions; move to RqRsInvLock.v *)
Ltac disc_lock_conds :=
  match goal with
  | [H: OLockedTo _ _ _ |- _] => red in H
  end.

(** TODO: add more conditions; move to RqRsInvMsg.v *)
Ltac disc_msgs_in :=
  match goal with
  | [H: RqUpMsgs _ _ _ |- _] =>
    let cidx := fresh "cidx" in
    let rqUp := fresh "rqUp" in
    destruct H as [cidx [rqUp ?]]; dest
  end.

Ltac disc_rqToUpRule :=
  match goal with
  | [H: RqToUpRule _ _ _ |- _] =>
    let rqFrom := fresh "rqFrom" in
    let rqTos := fresh "rqTos" in
    destruct H as [? [rqFrom [rqTos ?]]]
  end.

Lemma upLockedInv_False_1:
  forall dtr orqs msgs oidx rqUp rqm down rsm,
    UpLockedInv dtr orqs msgs oidx ->
    rqEdgeUpFrom dtr oidx = Some rqUp ->
    edgeDownTo dtr oidx = Some down ->
    InMP rqUp rqm msgs ->
    InMP down rsm msgs -> msg_type rsm = MRs ->
    False.
Proof.
  intros.
  destruct H as [rqUp' [down' [pidx ?]]]; dest.
  rewrite H in H0; inv H0.
  rewrite H5 in H1; inv H1.
  eapply xor3_False_1; [eassumption| |].
  - red in H2.
    destruct (findQ rqUp msgs).
    + intuition.
    + simpl in *; omega.
  - unfold rssQ in *; red in H3.
    clear -H3 H4 H8.
    induction (findQ down msgs).
    + intuition.
    + simpl in *.
      destruct H3; subst.
      * rewrite H4 in *; simpl in *; omega.
      * destruct (msg_type a ==n MRs); auto.
        simpl in *; omega.
Qed.

Section RqUpInd.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).

  Lemma rqUp_set:
    forall oidxTo rqUps,
      RqUpMsgs dtr oidxTo rqUps ->
      forall oidx ridx rins routs st1 st2,
        SubList rqUps routs ->
        Reachable (steps step_m) sys st1 ->
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        RqUpMsgs dtr oidx rins /\
        routs = rqUps /\
        exists rqUp rqm rsbTo,
          rqUps = [(rqUp, rqm)] /\
          OLockedTo st2.(bst_orqs) oidx rsbTo /\
          rqEdgeUpFrom dtr oidx = Some rqUp /\
          length (findQ rqUp st2.(bst_msgs)) = 1.
  Proof.
    intros.
    destruct Hrrs as [? [? ?]].

    assert (UpLockInv dtr sys st2) as Hlock.
    { apply upLockInv_ok; auto.
      eapply reachable_steps; [eassumption|].
      econstructor; eauto.
      econstructor.
    }

    inv H2; simpl in *.
    destruct H as [oidx [[rqUp rqm] ?]];
      dest; simpl in *; subst; simpl in *.
    
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - exfalso; disc_rule_conds.
      apply SubList_singleton in H0; inv H0.
      disc_rule_conds.
    - exfalso; disc_rule_conds.
      apply SubList_singleton in H0; inv H0.
      disc_rule_conds.

    - disc_rule_conds.
      + (** The only non-"exfalso" case *)
        apply SubList_singleton in H0; inv H0.
        good_locking_get obj.

        (* TODO: better to have a discharger for [LockInv]? *)
        red in H; mred; simpl in H; mred.
        destruct H as [rqUp' [down [pidx ?]]]; dest.
        (* TODO ends here *)

        disc_footprints_ok.
        disc_rule_conds.

        repeat split.
        * exists cidx; eexists.
          repeat split; try assumption.
        * exists rqUp', rqtm, (rqi_midx_rsb rqi).
          repeat split.
          { red; mred; simpl; mred.
            exists rqi; split; auto.
          }
          { clear -H12.
            rewrite findQ_In_enqMP in *.
            rewrite app_length in H12; simpl in H12.
            rewrite app_length; simpl.
            omega.
          }
      + exfalso; disc_rule_conds.
        apply SubList_singleton_In in H0.
        red in H37; destruct H37 as [upCIdx ?]; dest.
        eapply RqRsDownMatch_rq_In in H15; [|apply in_map; eassumption].
        destruct H15 as [cidx ?]; dest.
        pose proof (rqrsDTree_rqUp_down_not_eq H3 _ _ H7 H26); auto.
      + exfalso; disc_rule_conds.
        apply SubList_singleton_In in H0.
        red in H37; destruct H37 as [upCIdx ?]; dest.
        eapply RqRsDownMatch_rq_In in H8; [|apply in_map; eassumption].
        destruct H8 as [cidx ?]; dest.
        pose proof (rqrsDTree_rqUp_down_not_eq H3 _ _ H7 H15); auto.

    - exfalso; disc_rule_conds.
      + apply SubList_singleton in H0; inv H0.
        disc_rule_conds.
      + apply SubList_singleton in H0; inv H0.
        disc_rule_conds.
    - exfalso; disc_rule_conds.
      apply SubList_singleton_In in H0.
      red in H26; destruct H26 as [upCIdx ?]; dest.
      eapply RqRsDownMatch_rq_In in H15; [|apply in_map; eassumption].
      destruct H15 as [cidx ?]; dest.
      pose proof (rqrsDTree_rqUp_down_not_eq H3 _ _ H7 H24); auto.
  Qed.

  Lemma rqUp_atomic_eouts:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall oidxTo rqUps,
        RqUpMsgs dtr oidxTo rqUps ->
        SubList rqUps eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          steps step_m sys st1 hst st2 ->
          eouts = rqUps.
  Proof.
    induction 1; simpl; intros; subst.
    - inv H2; inv H6.
      eapply rqUp_set in H8; try eassumption; dest.
      assumption.
    - destruct H5 as [cidx [rqUp ?]]; dest; subst.
      inv H8.
      apply SubList_singleton_In in H6.
      apply in_app_or in H6; destruct H6.
      + exfalso.
        pose proof (removeL_In_2 _ _ _ _ H2).
        assert (RqUpMsgs dtr oidxTo [rqUp] /\ SubList [rqUp] eouts).
        { split.
          { exists cidx, rqUp; repeat split; assumption. }
          { red; intros; Common.dest_in; assumption. }
        }
        destruct H8.
        specialize (IHAtomic _ _ H8 H9 _ _ H7 H11); subst.
        assert (rins = [rqUp]); subst.
        { inv H13; destruct H22; red in H12.
          clear -H0 H1 H12.
          destruct rins as [|rin1 rins]; [elim H0; reflexivity|].
          destruct rins as [|rin2 rins].
          { apply SubList_singleton in H1; subst; reflexivity. }
          { inv H12.
            pose proof (H1 rin1 (or_introl eq_refl)).
            pose proof (H1 rin2 (or_intror (or_introl eq_refl))).
            Common.dest_in.
            elim H3; simpl; tauto.
          }
        }
        rewrite removeL_nil in H2; inv H2.
      + assert (RqUpMsgs dtr oidxTo [rqUp] /\ SubList [rqUp] routs).
        { split.
          { exists cidx, rqUp; repeat split; assumption. }
          { red; intros; Common.dest_in; assumption. }
        }
        destruct H6.
        eapply rqUp_set in H13; try eassumption; eauto.
        dest; subst.
        specialize (IHAtomic _ _ H9 H1 _ _ H7 H11); subst.
        rewrite removeL_nil; reflexivity.
  Qed.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_msgs_in.
  
  Lemma rqUpMsgs_RqToUpRule:
    forall oidx {oifc} (rule: Rule oifc) post porq rins nost norq routs oidxTo,
      GoodRqRsRule dtr oidx rule ->
      rule_precond rule post porq rins ->
      rule_trs rule post porq rins = (nost, norq, routs) ->
      RqUpMsgs dtr oidxTo routs ->
      RqToUpRule dtr oidx rule.
  Proof.
    intros; destruct Hrrs as [? [? ?]].
    good_rqrs_rule_cases rule.
    - exfalso; disc_rule_conds.
    - exfalso; disc_rule_conds.
    - destruct H.
      split; try assumption.
      destruct H6 as [|[|]].
      + eauto.
      + exfalso; disc_rule_conds.
        eapply RqRsDownMatch_rq_In in H8; [|left; reflexivity].
        destruct H8 as [cidx' ?]; dest.
        elim (rqrsDTree_rqUp_down_not_eq H3 _ _ H14 H15); reflexivity.
      + exfalso; disc_rule_conds.
        eapply RqRsDownMatch_rq_In in H7; [|left; reflexivity].
        destruct H7 as [cidx' ?]; dest.
        elim (rqrsDTree_rqUp_down_not_eq H3 _ _ H12 H14); reflexivity.
    - exfalso; disc_rule_conds.
    - exfalso; disc_rule_conds.
      eapply RqRsDownMatch_rq_In in H9; [|left; reflexivity].
      destruct H9 as [cidx' ?]; dest.
      elim (rqrsDTree_rqUp_down_not_eq H3 _ _ H13 H14); reflexivity.
  Qed.

  Ltac disc_rule_custom ::=
    match goal with
    | [H: UpLockFreeSuff _ |- _] => red in H
    | [H: DownLockFreeSuff _ |- _] => red in H
    | [H: MsgOutsOrthORq _ |- _] => red in H
    end.

  Lemma rqUpUp_rqUpDown_reducible:
    forall oidx (rule1 rule2: Rule oifc),
      RqUpUp dtr oidx rule1 ->
      StateSilent rule1 -> MsgOutsOrthORq rule1 ->
      RqUpDown dtr oidx rule2 ->
      StateSilent rule2 -> MsgOutsOrthORq rule2 ->
      NonConflictingR rule1 rule2.
  Proof.
    intros.
    red; intros.
    split.
    - disc_rule_conds.
      eapply H12; [eassumption|mred].
    - remember (rule_trs rule2 nost1 norq1 ins2) as trs2.
      destruct trs2 as [[nost2 norq2] outs2]; apply eq_sym in Heqtrs2.
      remember (rule_trs rule2 post1 porq1 ins2) as rtrs2.
      destruct rtrs2 as [[rnost2 rnorq2] routs2]; apply eq_sym in Heqrtrs2.
      remember (rule_trs rule1 rnost2 rnorq2 ins1) as rtrs1.
      destruct rtrs1 as [[rnost1 rnorq1] routs1]; apply eq_sym in Heqrtrs1.

      assert (rule_precond rule2 post1 porq1 ins2)
        by (disc_rule_conds; eapply H12; [eassumption|mred]).
      assert (rule_precond rule1 rnost2 rnorq2 ins1)
        by (disc_rule_conds; eapply H10; [eassumption|mred]).
      disc_rule_conds.

      specialize (H1 nost2 porq1 (porq1 +[downRq <- rqi2]) [(rqFrom, rqi_msg rqi)]).
      rewrite H6, Heqrtrs1 in H1; simpl in H1; inv H1.

      specialize (H4 nost2 porq1 (porq1 +[upRq <- rqi]) [(rqFrom1, rqi_msg rqi1)]).
      rewrite Heqtrs2, Heqrtrs2 in H4; simpl in H4; inv H4.

      repeat split.
      + eapply H11; [eassumption|mred].
      + f_equal; meq.
        * destruct rqi1 as [rqim1 rss1 rsb1].
          destruct rqi2 as [rqim2 rss2 rsb2].
          simpl in *; subst.
          destruct Hrrs as [? _].
          pose proof (footprintUpDownOk_rs_eq H0 H60 H66); dest; subst.
          reflexivity.
        * destruct rqi as [rqim rss rsb].
          destruct rqi0 as [rqim0 rss0 rsb0].
          simpl in *; subst.
          destruct Hrrs as [? _].
          pose proof (footprintUpOk_rs_eq H0 H48 H54); dest; subst.
          reflexivity.
  Qed.

  Lemma rqUpUp_rqDownDown_reducible:
    forall oidx (rule1 rule2: Rule oifc),
      RqUpUp dtr oidx rule1 ->
      StateSilent rule1 -> MsgOutsOrthORq rule1 ->
      RqDownDown dtr oidx rule2 ->
      StateSilent rule2 -> MsgOutsOrthORq rule2 ->
      NonConflictingR rule1 rule2.
  Proof.
    intros.
    red; intros.
    split.
    - disc_rule_conds.
      eapply H12; [eassumption|mred].
    - remember (rule_trs rule2 nost1 norq1 ins2) as trs2.
      destruct trs2 as [[nost2 norq2] outs2]; apply eq_sym in Heqtrs2.
      remember (rule_trs rule2 post1 porq1 ins2) as rtrs2.
      destruct rtrs2 as [[rnost2 rnorq2] routs2]; apply eq_sym in Heqrtrs2.
      remember (rule_trs rule1 rnost2 rnorq2 ins1) as rtrs1.
      destruct rtrs1 as [[rnost1 rnorq1] routs1]; apply eq_sym in Heqrtrs1.

      assert (rule_precond rule2 post1 porq1 ins2)
        by (disc_rule_conds; eapply H12; [eassumption|mred]).
      assert (rule_precond rule1 rnost2 rnorq2 ins1)
        by (disc_rule_conds; eapply H10; [eassumption|mred]).
      disc_rule_conds.

      specialize (H1 nost2 porq1 (porq1 +[downRq <- rqi2]) [(rqFrom, rqi_msg rqi)]).
      rewrite H6, Heqrtrs1 in H1; simpl in H1; inv H1.

      specialize (H4 nost2 porq1 (porq1 +[upRq <- rqi]) [(rqFrom1, rqi_msg rqi1)]).
      rewrite Heqtrs2, Heqrtrs2 in H4; simpl in H4; inv H4.

      repeat split.
      + eapply H11; [eassumption|mred].
      + f_equal; meq.
        * destruct rqi1 as [rqim1 rss1 rsb1].
          destruct rqi2 as [rqim2 rss2 rsb2].
          simpl in *; subst.
          destruct Hrrs as [? _].
          pose proof (footprintDownDownOk_rs_eq H0 H60 H66); dest; subst.
          reflexivity.
        * destruct rqi as [rqim rss rsb].
          destruct rqi0 as [rqim0 rss0 rsb0].
          simpl in *; subst.
          destruct Hrrs as [? _].
          pose proof (footprintUpOk_rs_eq H0 H48 H54); dest; subst.
          reflexivity.
  Qed.

  Ltac disc_rule_custom ::=
    try disc_lock_conds;
    try disc_footprints_ok;
    try disc_msgs_in.

  Lemma rqUp_lbl_reducible:
    forall oidxTo rqUps oidx1 ridx1 rins1 routs1,
      RqUpMsgs dtr oidxTo rqUps ->
      SubList rqUps routs1 ->
      forall oidx2 ridx2 rins2 routs2,
        DisjList routs1 rins2 ->
        Reducible
          sys [RlblInt oidx2 ridx2 rins2 routs2;
                 RlblInt oidx1 ridx1 rins1 routs1]
          [RlblInt oidx1 ridx1 rins1 routs1;
             RlblInt oidx2 ridx2 rins2 routs2].
  Proof.
    intros.
    destruct Hrrs as [? [? ?]].
    apply internal_steps_commutes; intros.

    (* Register necessary invariants. *)
    inv H6.
    pose proof (upLockInv_ok H3 H2 (reachable_steps H5 H10)) as HlockInv.
    pose proof (footprints_ok H3 (reachable_steps H5 H10)) as HftInv.
    
    inv_steps.
    pose proof (rqUp_set H H0 H5 H13).
    destruct H6 as [? [? [rqUp [rqm [rsbTo ?]]]]]; dest; subst.
    inv_step; simpl in *.
    good_rqrs_rule_get rule.
    eapply rqUpMsgs_RqToUpRule in H7; try eassumption.
    good_rqrs_rule_get rule0.

    destruct (eq_nat_dec (obj_idx obj) (obj_idx obj0)); subst.
    - red_obj_rule; rename obj0 into obj.
      good_rqrs_rule_cases rule0.

      + (** case [ImmDownRule] *)
        exfalso; disc_rule_conds.
        destruct H9; discriminate.

      + (** case [ImmUpRule] *)
        repeat split; try assumption.
        * assert (RsToUpRule dtr (obj_idx obj) rule0) by (left; assumption).
          good_rqUp_rsUp_get rule rule0.
          right; split; [reflexivity|].
          intros; red_obj_rule.
          assumption.
        * admit.
        * admit.

      + (** case [RqFwdRule] *)
        mred.
        destruct H8; destruct H12 as [|[|]].
        * (** case [RqUpUp] *)
          exfalso.
          disc_rqToUpRule.
          disc_rule_conds.

        * (** case [RqUpDown] *)
          repeat split; try assumption.
          { right; split; [reflexivity|].
            intros; red_obj_rule.
            destruct H7.
            red in H7, H8; dest.
            eapply rqUpUp_rqUpDown_reducible; eauto.
          }
          { admit. }
          { admit. }
          
        * (** case [RqDownDown] *)
          repeat split; try assumption.
          { right; split; [reflexivity|].
            intros; red_obj_rule.
            destruct H7.
            red in H7, H8; dest.
            eapply rqUpUp_rqDownDown_reducible; eauto.
          }
          { admit. }
          { admit. }

      + (** case [RsBackRule] *)
        good_footprint_get (obj_idx obj).
        mred.
        destruct H8; destruct H8; dest.
        * (** case [FootprintReleasingUp] *)
          exfalso; disc_rule_conds.
          destruct (eq_nat_dec cidx0 (obj_idx obj));
            [subst|elim (rqrsDTree_rqUp_rqUp_not_eq H2 n H39 H10); reflexivity].
          good_locking_get obj.
          red in H21; mred; simpl in H21.
          rewrite H40 in H21.
          eapply upLockedInv_False_1; eauto.
          { apply InMP_or_enqMP; auto. }
          { apply FirstMP_InMP; auto. }

        * (** case [FootprintReleasingDown] *)
          assert (RsToUpRule dtr (obj_idx obj) rule0) by (right; eauto).
          
          repeat split; try assumption.
          { good_rqUp_rsUp_get rule rule0.
            right; split; [reflexivity|].
            intros; red_obj_rule.
            assumption.
          }
          { admit. }
          { admit. }

      + (** case [RsDownRqDownRule] *)
        exfalso; disc_rule_conds.
        destruct (eq_nat_dec cidx0 (obj_idx obj));
          [subst|elim (rqrsDTree_rqUp_rqUp_not_eq H2 n H39 H10); reflexivity].
        good_locking_get obj.
        red in H; mred; simpl in H.
        rewrite H45 in H.
        eapply upLockedInv_False_1; eauto.
        { apply InMP_or_enqMP; auto. }
        { apply FirstMP_InMP; auto. }

    - repeat split; try assumption.
      + red; auto.
      (** TODO: need to know if [oidx1 <> oidx2] then [rins1 -*- rins2] 
       * and [routs1 -*- routs2]. *)
      + admit.
      + admit.
      
  Admitted.
  
  Lemma rqUp_lpush_lbl:
    forall pinits pins phst pouts peouts,
      Atomic msg_dec pinits pins phst pouts peouts ->
      forall oidxTo rqUps,
        RqUpMsgs dtr oidxTo rqUps ->
        SubList rqUps peouts ->
        forall oidx ridx rins routs,
          DisjList peouts rins ->
          Reducible sys (RlblInt oidx ridx rins routs :: phst)
                    (phst ++ [RlblInt oidx ridx rins routs]).
  Proof.
    induction 1; simpl; intros; subst.
    - eapply rqUp_lbl_reducible; eauto.
    - eapply reducible_trans.
      + apply reducible_cons_2.
        eapply rqUp_lbl_reducible; admit.
      + apply reducible_cons.
        eapply IHAtomic.

        (** TODO: need to prove [peouts = rqUps = [rqUp]]. *)
      
  Admitted.
  
  Lemma rqUp_lpush_unit_ok_ind:
    forall oidxTo rqUps inits ins hst outs eouts
           pinits pins phst pouts peouts,
      Atomic msg_dec pinits pins phst pouts peouts ->
      RqUpMsgs dtr oidxTo rqUps ->
      SubList rqUps peouts ->
      Atomic msg_dec inits ins hst outs eouts ->
      DisjList peouts inits ->
      Reducible sys (hst ++ phst) (phst ++ hst).
  Proof.
    induction 4; simpl; intros; subst.
    - eapply rqUp_lpush_lbl; eauto.
    - eapply reducible_trans.
      + change (RlblInt oidx ridx rins routs :: hst ++ phst)
          with ([RlblInt oidx ridx rins routs] ++ hst ++ phst).
        apply reducible_app_1.
        apply IHAtomic; auto.
      + replace (phst ++ RlblInt oidx ridx rins routs :: hst)
          with ((phst ++ [RlblInt oidx ridx rins routs]) ++ hst)
          by (rewrite <-app_assoc; reflexivity).
        rewrite app_assoc.
        apply reducible_app_2.
        eapply rqUp_lpush_lbl; eauto.
        apply DisjList_comm.
        eapply DisjList_SubList; [eassumption|].

        (** TODO: need to prove this admit *)
        admit.
  Admitted.
  
End RqUpInd.

Section Pushable.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).

  Variables (phst: MHistory)
            (oidx ridx: IdxT)
            (rins routs: list (Id Msg)).
  Hypothesis (Hcont: ValidExtContinuousL
                       sys phst (RlblInt oidx ridx rins routs)).

  Local Definition nlbl := (RlblInt oidx ridx rins routs).

  Section RqUp.
    Hypothesis (Hru: RqUpMsgs dtr oidx rins).

    Definition RqUpLPush (hst: MHistory): Prop :=
      True. (* always left-pushable *)

    Definition RqUpRPush (hst: MHistory): Prop :=
      False. (* no right-pushable histories *)

    Lemma rqUp_lpush_or_rpush:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst => RqUpLPush hst \/ RqUpRPush hst) hsts.
    Proof.
      intros; clear.
      apply Forall_forall; intros.
      left; red; auto.
    Qed.
    
    Lemma rqUp_lpush_unit_ok:
      forall inits ins hst outs eouts,
        Atomic msg_dec inits ins hst outs eouts ->
        Discontinuous phst hst ->
        Reducible sys (hst ++ phst) (phst ++ hst).
    Proof.
      intros.
      destruct Hcont; clear H2.
      destruct H1 as [peouts [oidx' [ridx' [rins' [routs' ?]]]]]; dest.
      apply eq_sym in H2; inv H2.
      destruct H1 as [pinits pins phst pouts peouts].
      red in H0; dest.
      pose proof (atomic_unique H0 H2); dest; subst.
      pose proof (atomic_unique H5 H); dest; subst.
      eapply rqUp_lpush_unit_ok_ind; eauto.
      apply DisjList_comm; assumption.
    Qed.
    
    Lemma rqUp_lpush_ok:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst =>
                    RqUpLPush hst ->
                    Reducible sys (hst ++ phst) (phst ++ hst)) hsts.
    Proof.
      intros.
      inv H1; clear H8.
      generalize dependent st3.
      induction hsts; simpl; intros; [constructor|].

      inv H0; inv H2.
      rewrite <-app_assoc in H6.
      eapply steps_split in H6; [|reflexivity].
      destruct H6 as [sti [? ?]].

      constructor; eauto.
      intros; inv H4; dest.
      eapply rqUp_lpush_unit_ok; eauto.
    Qed.

    Lemma rqUp_rpush_ok:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst =>
                    RqUpRPush hst ->
                    Reducible sys (nlbl :: hst) (hst ++ [nlbl])) hsts.
    Proof.
      intros; clear.
      apply Forall_forall; intros.
      red in H0; elim H0.
    Qed.

    Lemma rqUp_LRPushable:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          LRPushable sys RqUpLPush RqUpRPush hsts.
    Proof.
      intros; red; intros; subst.
      red in H5; elim H5.
    Qed.

  End RqUp.

  Section RsUp.
    Hypothesis (Hru: RsUpMsgs dtr oidx rins).

    Definition RsUpLPush (hst: MHistory): Prop :=
      False. (* no left-pushable histories *)

    Definition RsUpRPush (hst: MHistory): Prop :=
      True. (* always right-pushable *)

    Lemma rsUp_lpush_or_rpush:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst => RsUpLPush hst \/ RsUpRPush hst) hsts.
    Proof.
      intros; clear.
      apply Forall_forall; intros.
      right; red; auto.
    Qed.

    Lemma rsUp_lpush_ok:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst =>
                    RsUpLPush hst ->
                    Reducible sys (hst ++ phst) (phst ++ hst)) hsts.
    Proof.
      intros; clear.
      apply Forall_forall; intros.
      red in H0; elim H0.
    Qed.

    Lemma rsUp_rpush_ok:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          Forall (fun hst =>
                    RsUpRPush hst ->
                    Reducible sys (nlbl :: hst) (hst ++ [nlbl])) hsts.
    Proof.
    Admitted.

    Lemma rsUp_LRPushable:
      forall st1,
        Reachable (steps step_m) sys st1 ->
        forall hsts st2,
          Forall (AtomicEx msg_dec) hsts ->
          steps step_m sys st1 (nlbl :: List.concat hsts ++ phst) st2 ->
          Forall (fun hst => Discontinuous phst hst) hsts ->
          LRPushable sys RsUpLPush RsUpRPush hsts.
    Proof.
      intros; red; intros; subst.
      red in H4; elim H4.
    Qed.
    
  End RsUp.

End Pushable.

Theorem rqrs_pushable:
  forall {oifc} (sys: System oifc) (dtr: DTree),
    RqRsSys dtr sys ->
    Pushable sys.
Proof.
  intros; red; intros.

  assert (exists oidx ridx rins routs,
             l2 = RlblInt oidx ridx rins routs /\
             (RqUpMsgs dtr oidx rins \/
              RqDownMsgs dtr oidx rins \/
              RsUpMsgs dtr oidx rins \/
              RsDownMsgs dtr oidx rins)) as Hnlbl.
  { inv H0; inv H1.
    destruct H0 as [oidx [ridx [rins [routs ?]]]]; dest; subst.
    do 4 eexists; split; auto.
    destruct H as [? [? ?]].
    inv H5.
    eapply messages_in_cases.
    { eassumption. }
    { eapply reachable_steps; eassumption. }
    { eassumption. }
  }
  destruct Hnlbl as [oidx [ridx [rins [routs ?]]]]; dest; subst.

  destruct H2 as [|[|[|]]].

  - exists RqUpLPush, RqUpRPush.
    repeat split.
    + eauto using rqUp_lpush_or_rpush.
    + eauto using rqUp_lpush_ok.
    + eauto using rqUp_rpush_ok.
    + eauto using rqUp_LRPushable.

  - admit.

  - exists RsUpLPush, RsUpRPush.
    repeat split.
    + eauto using rsUp_lpush_or_rpush.
    + eauto using rsUp_lpush_ok.
    + eauto using rsUp_rpush_ok.
    + eauto using rsUp_LRPushable.

  - admit.
      
Admitted.

Corollary rqrs_serializable:
  forall {oifc} (sys: System oifc) (dtr: DTree),
    RqRsSys dtr sys ->
    SerializableSys sys.
Proof.
  intros.
  apply well_interleaved_serializable.
  apply well_interleaved_push_ok.
  eapply rqrs_pushable; eauto.
Qed.

Close Scope list.
Close Scope fmap.

