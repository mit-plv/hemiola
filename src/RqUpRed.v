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

Section RqUpReduction.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).

  Ltac disc_rule_custom ::=
    try disc_lock_conds;
    try disc_footprints_ok.

  Lemma rqUpUp_rqUpMsgs:
    forall oidx ridx rins routs st1 st2 obj rule,
      Reachable (steps step_m) sys st1 ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      In obj sys.(sys_objs) -> obj.(obj_idx) = oidx ->
      In rule obj.(obj_rules) -> rule.(rule_idx) = ridx ->
      RqUpUp dtr oidx rule -> RqFwdRuleCommon rule ->
      exists oidxTo, RqUpMsgs dtr oidxTo routs.
  Proof.
    intros; destruct Hrrs as [? [? ?]].
    inv_step.
    red_obj_rule.
    disc_rule_conds.
    pose proof (rqEdgeUpFrom_Some H7 _ H2).
    destruct H11 as [rsUp [down [pidx ?]]]; dest.
    repeat disc_rule_minds.
    exists pidx.
    red; do 2 eexists; repeat split; try eassumption.
  Qed.
  
  Lemma rqUp_spec:
    forall oidxTo rqUps,
      RqUpMsgs dtr oidxTo rqUps ->
      forall oidx ridx rins routs st1 st2,
        SubList rqUps routs ->
        Reachable (steps step_m) sys st1 ->
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        RqUpMsgs dtr oidx rins /\
        parentIdxOf dtr oidx = Some oidxTo /\
        routs = rqUps /\
        exists cidx rqFrom rqfm rqTo rqtm down orq rqiu,
          rins = [(rqFrom, rqfm)] /\
          parentIdxOf dtr cidx = Some oidx /\
          rqEdgeUpFrom dtr cidx = Some rqFrom /\
          edgeDownTo dtr cidx = Some down /\
          rqUps = [(rqTo, rqtm)] /\
          st2.(bst_orqs)@[oidx] = Some orq /\
          orq@[upRq] = Some rqiu /\ rqiu.(rqi_midx_rsb) = down /\
          rqEdgeUpFrom dtr oidx = Some rqTo /\
          length (findQ rqTo st2.(bst_msgs)) = 1.
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
        disc_rule_conds.
        repeat split.
        * exists cidx; eexists.
          repeat split; try assumption.
        * do 8 eexists.
          repeat split; try eassumption.
          { mred. }
          { clear -H24.
            rewrite findQ_In_enqMP in *.
            rewrite app_length in H24; simpl in H24.
            rewrite app_length; simpl.
            omega.
          }

      + exfalso; disc_rule_conds.
        apply SubList_singleton_In in H0.
        eapply RqRsDownMatch_rq_rs in H24; [|apply in_map; eassumption].
        destruct H24 as [cidx [rsUp ?]]; dest.
        pose proof (rqrsDTree_rqUp_down_not_eq H3 _ _ H7 H24); auto.
      + exfalso; disc_rule_conds.
        apply SubList_singleton_In in H0.
        eapply RqRsDownMatch_rq_rs in H9; [|apply in_map; eassumption].
        destruct H9 as [cidx [rsUp ?]]; dest.
        pose proof (rqrsDTree_rqUp_down_not_eq H3 _ _ H7 H15); auto.

    - exfalso; disc_rule_conds.
      + apply SubList_singleton in H0; inv H0.
        disc_rule_conds.
      + apply SubList_singleton in H0; inv H0.
        disc_rule_conds.
    - exfalso; disc_rule_conds.
      apply SubList_singleton_In in H0.
      eapply RqRsDownMatch_rq_rs in H24; [|apply in_map; eassumption].
      destruct H24 as [cidx [down ?]]; dest.
      pose proof (rqrsDTree_rqUp_down_not_eq H3 _ _ H7 H25); auto.
  Qed.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_msgs_in.
  
  Lemma rqUpMsgs_RqToUpRule:
    forall {oifc} (sys: System oifc) oidx (rule: Rule oifc)
           post porq rins nost norq routs oidxTo,
      GoodRqRsRule dtr sys oidx rule ->
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
        eapply RqRsDownMatch_rq_rs in H12; [|left; reflexivity].
        destruct H12 as [cidx' [rsUp ?]]; dest.
        elim (rqrsDTree_rqUp_down_not_eq H3 _ _ H18 H12); reflexivity.
      + exfalso; disc_rule_conds.
        eapply RqRsDownMatch_rq_rs in H7; [|left; reflexivity].
        destruct H7 as [cidx' [rsUp ?]]; dest.
        elim (rqrsDTree_rqUp_down_not_eq H3 _ _ H12 H14); reflexivity.
    - exfalso; disc_rule_conds.
    - exfalso; disc_rule_conds.
      eapply RqRsDownMatch_rq_rs in H12; [|left; reflexivity].
      destruct H12 as [cidx' [rsUp ?]]; dest.
      elim (rqrsDTree_rqUp_down_not_eq H3 _ _ H15 H12); reflexivity.
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
      RqUpDown dtr sys oidx rule2 ->
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
    try disc_msgs_in;
    try disc_rqToUpRule.

  Lemma rqUp_lbl_commutes:
    forall oidxTo rqUps st1 st2 oidx1 ridx1 rins1 routs1 oidx2 ridx2 rins2 routs2,
      RqUpMsgs dtr oidxTo rqUps ->
      SubList rqUps routs1 ->
      DisjList routs1 rins2 ->
      Reachable (steps step_m) sys st1 ->
      steps step_m sys st1
            [RlblInt oidx2 ridx2 rins2 routs2;
               RlblInt oidx1 ridx1 rins1 routs1] st2 ->
      NonConflictingL sys oidx1 ridx1 oidx2 ridx2 /\
      DisjList (idsOf rins1) (idsOf rins2) /\
      DisjList routs1 rins2 /\
      DisjList (idsOf routs1) (idsOf routs2).
  Proof.
    intros; destruct Hrrs as [? [? ?]].
    
    (* Register necessary invariants. *)
    inv H3.
    pose proof (upLockInv_ok H5 H4 (reachable_steps H2 H10)) as HlockInv.
    pose proof (footprints_ok H5 (reachable_steps H2 H10)) as HftInv.
    
    inv_steps.
    pose proof (rqUp_spec H H0 H2 H13).
    destruct H3 as [? [? [? ?]]].
    destruct H9 as [cidx [rqFrom [rqfm [rqTo [rqtm [down [orq [rqiu ?]]]]]]]].
    dest; subst.
    inv_step; simpl in *.
    good_rqrs_rule_get rule.
    eapply rqUpMsgs_RqToUpRule in H8; try eassumption.
    good_rqrs_rule_get rule0.

    destruct (eq_nat_dec (obj_idx obj) (obj_idx obj0)); subst.
    - red_obj_rule; rename obj0 into obj.
      good_rqrs_rule_cases rule0.

      + (** case [ImmDownRule] *)
        exfalso; disc_rule_conds.

      + (** case [ImmUpRule] *)
        assert (RsToUpRule dtr (obj_idx obj) rule0) by (left; assumption).
        good_rqUp_rsUp_get rule rule0.
        disc_rule_conds.
        repeat split; try assumption.
        * right; split; [reflexivity|].
          intros; red_obj_rule.
          assumption.
        * solve_midx_disj.
        * solve_midx_disj.

      + (** case [RqFwdRule] *)
        mred.
        destruct H9; destruct H12 as [|[|]].
        * (** case [RqUpUp] *)
          exfalso; disc_rule_conds.

        * (** case [RqUpDown] *)
          repeat split; try assumption.
          { right; split; [reflexivity|].
            intros; red_obj_rule.
            destruct H8.
            red in H8, H9; dest.
            eapply rqUpUp_rqUpDown_reducible; eauto.
          }
          { disc_rule_conds.
            destruct (eq_nat_dec upCObj.(obj_idx) cidx1); subst.
            { exfalso.
              good_locking_get upCObj.
              red in H.
              apply parentIdxOf_not_eq in H15;
                [|destruct Hrrs as [[? ?] _]; assumption]; mred.
              find_if_inside.
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                eapply xor3_False_2; [eassumption| |].
                { eapply findQ_length_one; eauto. }
                { red; mred; simpl; mred; eauto. }
              }
              { destruct H; [congruence|].
                destruct H as [upRq [down [pidx ?]]]; dest.
                disc_rule_conds.
                eapply FirstMP_findQ_False; eauto.
              }
            }
            { solve_midx_disj. }
          }
          { disc_rule_conds; solve_midx_disj. }
          
        * (** case [RqDownDown] *)
          repeat split; try assumption.
          { right; split; [reflexivity|].
            intros; red_obj_rule.
            destruct H8.
            red in H8, H9; dest.
            eapply rqUpUp_rqDownDown_reducible; eauto.
          }
          { disc_rule_conds; solve_midx_disj. }
          { disc_rule_conds; solve_midx_disj. }

      + (** case [RsBackRule] *)
        good_footprint_get (obj_idx obj).
        mred; destruct H9; destruct H9; dest.
        * (** case [FootprintReleasingUp] *)
          exfalso; disc_rule_conds.
          good_locking_get obj.
          disc_lock_conds.
          eapply upLockedInv_False_1; eauto.
          { apply InMP_or_enqMP; auto. }
          { apply FirstMP_InMP; auto. }

        * (** case [FootprintReleasingDown] *)
          assert (RsToUpRule dtr (obj_idx obj) rule0) by (right; eauto).
          good_rqUp_rsUp_get rule rule0.
          disc_rule_conds.
          { repeat split; try assumption.
            { right; split; [reflexivity|].
              intros; red_obj_rule.
              assumption.
            }
            { rewrite H49; solve_midx_disj. }
            { solve_midx_disj. }
          }
          { repeat split; try assumption.
            { right; split; [reflexivity|].
              intros; red_obj_rule.
              assumption.
            }
            { rewrite H49; solve_midx_disj. }
            { solve_midx_disj. }
          }

      + (** case [RsDownRqDownRule] *)
        exfalso; disc_rule_conds.
        good_locking_get obj.
        disc_lock_conds.
        eapply upLockedInv_False_1; eauto.
        { apply InMP_or_enqMP; auto. }
        { apply FirstMP_InMP; auto. }

    - (* Better to extract as a lemma for arbitrary [Rule]s? *)
      split; [red; auto|].
      good_footprint_get (obj_idx obj0).
      good_rqrs_rule_cases rule0.
      + disc_rule_conds.
        destruct (eq_nat_dec cidx0 cidx2);
          [subst; rewrite H56 in H15; elim n; inv H15; reflexivity|].
        split; [|split]; [|assumption|]; solve_midx_disj.
      + disc_rule_conds.
        split; [|split]; [|assumption|]; solve_midx_disj.
      + disc_rule_conds.
        * destruct (eq_nat_dec cidx2 cidx0);
            [subst; rewrite H9 in H48; elim n; inv H48; reflexivity|].
          split; [|split]; [|assumption|]; solve_midx_disj.
        * destruct (eq_nat_dec cidx1 (obj_idx upCObj));
            [subst; rewrite H48 in H30; elim n; inv H30; reflexivity|].
          split; [|split]; [|assumption|]; solve_midx_disj.
        * split; [|split]; [|assumption|]; solve_midx_disj.
      + disc_rule_conds.
        * split; [|split]; [|assumption|]; solve_midx_disj.
        * rewrite H50.
          split; [|split]; [|assumption|]; solve_midx_disj.
        * rewrite H50.
          split; [|split]; [|assumption|]; solve_midx_disj.
      + disc_rule_conds.
        split; [|split]; [|assumption|]; solve_midx_disj.
  Qed.

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
    eapply rqUp_lbl_commutes; eauto.
  Qed.

  Inductive RqUpHistory: MHistory -> list (Id Msg) -> Prop :=
  | RqUpIntro:
      forall oidx ridx rins routs oidxTo,
        RqUpMsgs dtr oidxTo routs ->
        RqUpHistory [RlblInt oidx ridx rins routs] routs
  | RqUpCont:
      forall phst pouts oidx ridx rins routs oidxTo,
        RqUpHistory phst pouts ->
        rins = pouts ->
        RqUpMsgs dtr oidxTo routs ->
        RqUpHistory (RlblInt oidx ridx rins routs :: phst) routs.

  Lemma rqUp_atomic:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall oidxTo rqUps,
        RqUpMsgs dtr oidxTo rqUps ->
        SubList rqUps eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          steps step_m sys st1 hst st2 ->
          eouts = rqUps /\ RqUpHistory hst eouts.
  Proof.
    induction 1; simpl; intros; subst.
    - inv_steps.
      eapply rqUp_spec in H8; try eassumption.
      destruct H8 as [? [? [? ?]]].
      destruct H5 as [cidx [rqFrom [rqfm [rqTo [rqtm [down [orq [rqiu ?]]]]]]]].
      dest; subst.
      split; [reflexivity|econstructor; eauto].
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
        specialize (IHAtomic _ _ H8 H9 _ _ H7 H11); dest.
        assert (exists oidxTo, RqUpMsgs dtr oidxTo eouts)
          by (inv H12; eauto).
        destruct H14 as [poidxTo ?].
        destruct H14 as [pcidx [prqUp ?]]; dest; subst.
        inv H14.
        inv H13; destruct H26; red in H13.
        clear -H0 H1 H2 H13.
        destruct rins as [|rin1 rins]; [elim H0; reflexivity|].
        destruct rins as [|rin2 rins].
        * apply SubList_singleton in H1; subst.
          rewrite removeL_nil in H2; elim H2.
        * inv H13.
          pose proof (H1 rin1 (or_introl eq_refl)).
          pose proof (H1 rin2 (or_intror (or_introl eq_refl))).
          Common.dest_in.
          elim H4; simpl; tauto.
      + assert (RqUpMsgs dtr oidxTo [rqUp] /\ SubList [rqUp] routs).
        { split.
          { exists cidx, rqUp; repeat split; assumption. }
          { red; intros; Common.dest_in; assumption. }
        }
        destruct H6.
        eapply rqUp_spec in H13; eauto.
        destruct H13 as [? [? [? ?]]].
        destruct H13 as [cidx' [rqFrom [rqfm [rqTo [rqtm [down [orq [rqiu ?]]]]]]]].
        dest; subst.
        specialize (IHAtomic _ _ H9 H1 _ _ H7 H11); dest; subst.
        rewrite removeL_nil; simpl.
        split; [reflexivity|econstructor; eauto].
  Qed.

  Lemma rqUp_ins_disj:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall cidx corq pidx porq rqUp down prqi,
        parentIdxOf dtr cidx = Some pidx ->
        rqEdgeUpFrom dtr cidx = Some rqUp ->
        edgeDownTo dtr cidx = Some down ->
        st1.(bst_orqs)@[cidx] = Some corq -> corq@[upRq] <> None ->
        st1.(bst_orqs)@[pidx] = Some porq ->
        porq@[upRq] = Some prqi -> prqi.(rqi_midx_rsb) = down ->
        forall oidx ridx rins routs st2,
          step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
          DisjList (idsOf rins) [rqUp].
  Proof.
    intros; destruct Hrrs as [? [? ?]].

    inv_step; simpl in *.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - (** case [ImmDownRule] *)
      disc_rule_conds.
      destruct (eq_nat_dec cidx0 cidx);
        subst; [|solve_midx_disj].
      exfalso.
      rewrite H2 in H38; inv H38.
      congruence.

    - (** case [ImmUpRule] *)
      disc_rule_conds.
      solve_midx_disj.

    - (** case [RqFwdRule] *)
      disc_rule_conds.
      + (** case [RqUpUp] *)
        destruct (eq_nat_dec cidx0 cidx);
          subst; [|solve_midx_disj].
        rewrite H0 in H7; inv H7.
        congruence.
      + (** case [RqUpDown] *)
        pose proof (upLockInv_ok H10 H9 H) as HlockInv.
        good_locking_get upCObj.
        destruct (eq_nat_dec (obj_idx upCObj) cidx);
          subst; [|solve_midx_disj].
        exfalso.
        rewrite H0 in H12; inv H12.
        rewrite H1 in H13; inv H13.
        red in H8; rewrite H3 in H8.
        simpl in H8.
        destruct (corq@[upRq]); [|elim H4; reflexivity].
        destruct H8 as [rqUp [down [pidx ?]]]; dest.
        rewrite H2 in H12; inv H12.
        rewrite H1 in H8; inv H8.
        rewrite H0 in H13; inv H13.
        eapply xor3_False_2; [eassumption| |].
        * eapply findQ_length_one; eauto.
        * red.
          rewrite H5; simpl.
          exists prqi; auto.
      + (** case [RqDownDown] *)
        solve_midx_disj.

    - pose proof (footprints_ok H10 H) as HftInv.
      good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + solve_midx_disj.
      + rewrite H35; solve_midx_disj.
      + rewrite H35; solve_midx_disj.

    - disc_rule_conds.
      solve_midx_disj.
  Qed.
  
  Lemma rqUpHistory_lpush_lbl:
    forall phst rqUps,
      RqUpHistory phst rqUps ->
      forall oidx ridx rins routs,
        DisjList rqUps rins ->
        forall st1,
          Reachable (steps step_m) sys st1 ->
          forall st2,
            steps step_m sys st1 (RlblInt oidx ridx rins routs :: phst) st2 ->
            steps step_m sys st1 (phst ++ [RlblInt oidx ridx rins routs]) st2.
  Proof.
    induction 1; simpl; intros; subst.
    - eapply rqUp_lbl_reducible; eauto.
      apply SubList_refl.
    - eapply reducible_trans; eauto.
      + apply reducible_cons_2.
        eapply rqUp_lbl_reducible; eauto.
        apply SubList_refl.
      + destruct Hrrs as [? [? ?]].
        apply reducible_cons.
        red; intros.
        eapply IHRqUpHistory; eauto.

        assert (exists coidx cridx crins pphst coidxTo,
                   phst = RlblInt coidx cridx crins pouts :: pphst /\
                   RqUpMsgs dtr coidxTo pouts)
          by (inv H; do 5 eexists; eauto).
        destruct H8 as [coidx [cridx [crins [pphst [coidxTo ?]]]]]; dest; subst.
        clear H7; inv_steps.

        assert (Reachable (steps step_m) sys st7).
        { eapply reachable_steps; [apply H3|eassumption]. }

        pose proof H14 as Hru.
        eapply rqUp_spec with (rqUps:= routs) in Hru; eauto;
          [|apply SubList_refl
           |eapply reachable_steps; eauto;
            apply steps_singleton; eassumption].
        destruct Hru as [? [? [? ?]]].
        destruct H12 as [cidx [rqFrom [rqfm [rqTo [rqtm [down [orq [rqiu ?]]]]]]]].
        dest; subst.

        pose proof H15 as Hru.
        eapply rqUp_spec with (rqUps:= [(rqFrom, rqfm)]) in Hru; eauto;
          [|apply SubList_refl].
        destruct Hru as [? [? [? ?]]].
        destruct H25 as [ccidx [crqFrom [crqfm [crqTo [crqtm [cdown [corq [crqiu ?]]]]]]]].
        dest; subst.

        inv H29.
        disc_rule_conds.
        apply DisjList_comm, idsOf_DisjList; simpl.
        eapply rqUp_ins_disj.
        * instantiate (1:= st5).
          eapply reachable_steps; [|apply steps_singleton; eassumption].
          eapply reachable_steps; [|apply steps_singleton; eassumption].
          assumption.
        * apply H26.
        * assumption.
        * eassumption.
        * instantiate (1:= corq).
          apply parentIdxOf_not_eq in H26;
            [|destruct Hrrs as [[? ?]]; assumption].
          clear H13 H15.
          inv_step; simpl in *.
          mred.
        * congruence.
        * instantiate (1:= orq); assumption.
        * eassumption.
        * reflexivity.
        * eassumption.
  Qed.
  
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
    intros.
    red; intros.
    inv H3.
    eapply rqUp_atomic in H; eauto.
    dest; subst.
    eapply rqUpHistory_lpush_lbl; eauto.
    econstructor; eauto.
  Qed.

  Lemma rqUp_outs_disj:
    forall oidxTo rqUp st1 st2 oidx ridx rins routs,
      RqUpMsgs dtr oidxTo [rqUp] ->
      Reachable (steps step_m) sys st1 ->
      InMPI st1.(bst_msgs) rqUp ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      DisjList routs [rqUp].
  Proof.
    intros; destruct Hrrs as [? [? ?]].
    pose proof (footprints_ok H4 H0).
    pose proof (upLockInv_ok H4 H3 H0).

    destruct H as [ruIdx [[rqUp' rqm] ?]]; dest.
    inv H; rename rqUp' into rqUp; simpl in *.
    apply idsOf_DisjList; simpl.
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds; solve_midx_disj.
    - disc_rule_conds; solve_midx_disj.

    - good_locking_get obj.
      disc_rule_conds.
      + (* [RqUpUp] is the only case that requires [UpLockInv] 
         * to draw a contradiction. *)
        destruct (eq_nat_dec ruIdx (obj_idx obj));
          subst; [|solve_midx_disj].
        exfalso.
        destruct H2; [congruence|].
        destruct H2 as [orqUp [down [pidx ?]]]; dest.
        disc_rule_conds.
        eapply InMP_findQ_False; eauto.
      + solve_midx_disj.
      + solve_midx_disj.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds; solve_midx_disj.

    - disc_rule_conds; solve_midx_disj.
  Qed.

  Lemma rqUpHistory_outs:
    forall hst outs,
      RqUpHistory hst outs ->
      forall rqUp st1 st2,
        outs = [rqUp] ->
        steps step_m sys st1 hst st2 ->
        InMPI st2.(bst_msgs) rqUp.
  Proof.
    induction 1; simpl; intros; subst.
    - inv_steps; inv_step.
      destruct rqUp as [ruIdx rqm]; simpl in *.
      apply InMP_or_enqMP; auto.
    - inv_steps; inv_step.
      destruct rqUp as [ruIdx rqm]; simpl in *.
      apply InMP_or_enqMP; auto.
  Qed.
  
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
    - red; intros.

      assert (Reducible sys (RlblInt oidx ridx rins routs :: hst ++ phst)
                        (phst ++ RlblInt oidx ridx rins routs :: hst)); auto.

      eapply reducible_trans.
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

        inv_steps.
        clear H3 H4 H12 rins st2.
        eapply steps_split in H10; [|reflexivity].
        destruct H10 as [st2 [? ?]].
        eapply rqUp_atomic in H; eauto.
        dest; subst.
        destruct H0 as [ruIdx [[rqUp rqm] ?]]; dest; subst.
        simpl in *.

        assert (Reachable (steps step_m) sys st2)
          by (eapply reachable_steps; eauto).
        eapply rqUpHistory_outs in H5; [|reflexivity|eassumption].

        clear H1 H3 IHAtomic phst.
        generalize dependent st3.
        generalize dependent st2.
        induction H2; intros; subst.
        * inv_steps.
          eapply rqUp_outs_disj.
          { exists ruIdx, (rqUp, rqm); repeat split; eauto. }
          { apply H. }
          { assumption. }
          { eassumption. }
        * inv_steps.
          specialize (IHAtomic H8 _ H9 H10 _ H12).
          eapply (atomic_messages_in_in msg_dec) in H2; eauto;
            [|eapply DisjList_In_2; [eassumption|left; reflexivity]].
          apply DisjList_app_4; [apply removeL_DisjList; assumption|].
          eapply rqUp_outs_disj.
          { exists ruIdx, (rqUp, rqm); repeat split; eauto. }
          { eapply reachable_steps; eauto. }
          { assumption. }
          { eassumption. }
  Qed.
  
End RqUpReduction.

Close Scope list.
Close Scope fmap.

