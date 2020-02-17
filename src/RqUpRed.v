Require Import Peano_dec Omega List.
Require Import Common FMap IndexSupport.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.
Require Import RqRsInvMsg RqRsInvLock.

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
  forall `{dv: DecValue} dtr orqs msgs oidx rqUp rqm down rsm,
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
      * destruct (msg_type a); auto.
        simpl in *; omega.
Qed.

Section RqUpReduction.
  Context `{dv: DecValue} `{oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System).
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (oinvs: IdxT -> ObjInv)
             (Hrrs: RqRsSys dtr sys oinvs).

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
      routs <> nil /\ exists oidxTo, RqUpMsgs dtr oidxTo routs.
  Proof.
    intros; destruct Hrrs as [? [? ?]].
    inv_step.
    red_obj_rule.
    disc_rule_conds.
    - pose proof (rqEdgeUpFrom_Some (proj1 (proj2 H7)) _ H1).
      destruct H5 as [rsUp [down [pidx ?]]]; dest.
      repeat disc_rule_minds.
      split; [discriminate|].
      exists pidx.
      right; do 2 eexists; repeat split; try eassumption.
    - pose proof (rqEdgeUpFrom_Some (proj1 (proj2 H7)) _ H1).
      destruct H11 as [rsUp [down [pidx ?]]]; dest.
      repeat disc_rule_minds.
      split; [discriminate|].
      exists pidx.
      right; do 2 eexists; repeat split; try eassumption.
  Qed.

  Lemma rqUp_spec:
    forall oidxTo rqUps,
      rqUps <> nil ->
      RqUpMsgs dtr oidxTo rqUps ->
      forall oidx ridx rins routs st1 st2,
        SubList rqUps routs ->
        Reachable (steps step_m) sys st1 ->
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        RqUpMsgs dtr oidx rins /\
        parentIdxOf dtr oidx = Some oidxTo /\
        routs = rqUps /\
        (exists orq rqiu,
            st2.(st_orqs)@[oidx] = Some orq /\
            orq@[upRq] = Some rqiu /\
            ((rins = nil /\ rqiu.(rqi_midx_rsb) = None) \/
             exists cidx rqFrom rqfm down,
               rins = [(rqFrom, rqfm)] /\
               parentIdxOf dtr cidx = Some oidx /\
               rqEdgeUpFrom dtr cidx = Some rqFrom /\
               edgeDownTo dtr cidx = Some down /\
               rqiu.(rqi_midx_rsb) = Some down)) /\
        exists rqTo rqtm,
          rqUps = [(rqTo, rqtm)] /\
          rqEdgeUpFrom dtr oidx = Some rqTo /\
          length (findQ rqTo st2.(st_msgs)) = 1.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.

    assert (UpLockInv dtr sys st2) as Hlock.
    { apply upLockInv_ok; auto.
      eapply reachable_steps; [eassumption|].
      econstructor; eauto.
      econstructor.
    }

    inv_step; simpl in *.
    destruct H3; [exfalso; auto|].
    destruct H3 as [oidx [[rqUp rqm] ?]];
      dest; simpl in *; subst; simpl in *.
    
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - exfalso; disc_rule_conds.
      specialize (H4 _ (or_introl eq_refl)); dest_in.
    - exfalso; disc_rule_conds.

    - disc_rule_conds.
      + good_locking_get obj.
        disc_rule_conds.
        repeat split.
        * left; reflexivity.
        * do 2 eexists; repeat split.
          { mred. }
          { left; auto. }
        * do 2 eexists; repeat split.
          rewrite findQ_In_enqMP in *.
          rewrite app_length in H22; simpl in H22.
          rewrite app_length; simpl.
          omega.
        
      + good_locking_get obj.
        disc_rule_conds.
        repeat split.
        * right; do 2 eexists; repeat split; try eassumption.
        * do 2 eexists; repeat split.
          { mred. }
          { right; do 4 eexists; repeat split; try eassumption. }
        * do 2 eexists; repeat split.
          rewrite findQ_In_enqMP in *.
          rewrite app_length in H27; simpl in H27.
          rewrite app_length; simpl.
          omega.

      + exfalso; disc_rule_conds.
        apply SubList_singleton_In in H4.
        eapply RqRsDownMatch_rq_rs in H40; [|apply in_map; eassumption].
        destruct H40 as [cidx [rsUp ?]]; dest.
        solve_midx_false.
        
      + exfalso; disc_rule_conds.
        apply SubList_singleton_In in H4.
        eapply RqRsDownMatch_rq_rs in H25; [|apply in_map; eassumption].
        destruct H25 as [cidx [rsUp ?]]; dest.
        solve_midx_false.

      + exfalso; disc_rule_conds.
        apply SubList_singleton_In in H4.
        eapply RqRsDownMatch_rq_rs in H10; [|apply in_map; eassumption].
        destruct H10 as [cidx [rsUp ?]]; dest.
        solve_midx_false.
        
    - exfalso; disc_rule_conds.
      specialize (H4 _ (or_introl eq_refl)); dest_in.
      
    - exfalso; disc_rule_conds.
      apply SubList_singleton_In in H4.
      eapply RqRsDownMatch_rq_rs in H25; [|apply in_map; eassumption].
      destruct H25 as [cidx [down ?]]; dest.
      solve_midx_false.
  Qed.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_messages_in.
  
  Lemma rqUpMsgs_RqToUpRule:
    forall oidx (rule: Rule) post porq rins nost norq routs oidxTo,
      GoodRqRsRule dtr sys oidx rule ->
      rule_precond rule post porq rins ->
      rule_trs rule post porq rins = (nost, norq, routs) ->
      routs <> nil -> RqUpMsgs dtr oidxTo routs ->
      RqToUpRule dtr oidx rule.
  Proof.
    intros; destruct Hrrs as [? [? ?]].
    good_rqrs_rule_cases rule.
    - exfalso; disc_rule_conds; auto.
    - exfalso; disc_rule_conds; auto.
    - destruct H.
      split; try assumption.
      destruct H7 as [|[|]].
      + eauto.
      + exfalso; disc_rule_conds.
        * eapply RqRsDownMatch_rq_rs in H28; [|left; reflexivity].
          destruct H28 as [cidx' [rsUp ?]]; dest.
          solve_midx_false.
        * eapply RqRsDownMatch_rq_rs in H13; [|left; reflexivity].
          destruct H13 as [cidx' [rsUp ?]]; dest.
          solve_midx_false.
      + exfalso; disc_rule_conds.
        eapply RqRsDownMatch_rq_rs in H8; [|left; reflexivity].
        destruct H8 as [cidx' [rsUp ?]]; dest.
        solve_midx_false.
    - exfalso; disc_rule_conds.
    - exfalso; disc_rule_conds; auto.
      eapply RqRsDownMatch_rq_rs in H13; [|left; reflexivity].
      destruct H13 as [cidx' [rsUp ?]]; dest.
      solve_midx_false.
  Qed.

  Ltac disc_rule_custom ::=
    match goal with
    | [H: UpLockFreeSuff _ |- _] => red in H
    | [H: DownLockFreeSuff _ |- _] => red in H
    | [H: MsgOutsOrthORq _ |- _] => red in H
    end.

  Lemma rqUpUp_rqUpDown_reducible:
    forall oidx (rule1 rule2: Rule),
      RqUpUp dtr oidx rule1 ->
      StateSilent rule1 -> MsgOutsOrthORq rule1 ->
      RqUpDown dtr sys oidx rule2 ->
      StateSilent rule2 -> MsgOutsOrthORq rule2 ->
      NonConflictingR (oinvs oidx) rule1 rule2.
  Proof.
    intros.
    red; intros.
    split.
    - disc_rule_conds.
      + eapply H14; [eassumption|mred].
      + eapply H14; [eassumption|mred].
    - remember (rule_trs rule2 nost1 norq1 ins2) as trs2.
      destruct trs2 as [[nost2 norq2] outs2]; apply eq_sym in Heqtrs2.
      remember (rule_trs rule2 post1 porq1 ins2) as rtrs2.
      destruct rtrs2 as [[rnost2 rnorq2] routs2]; apply eq_sym in Heqrtrs2.
      remember (rule_trs rule1 rnost2 rnorq2 ins1) as rtrs1.
      destruct rtrs1 as [[rnost1 rnorq1] routs1]; apply eq_sym in Heqrtrs1.

      assert (rule_precond rule2 post1 porq1 ins2)
        by (disc_rule_conds; try (eapply H14; [eassumption|mred])).
      assert (rule_precond rule1 rnost2 rnorq2 ins1)
        by (disc_rule_conds; try (eapply H12; [eassumption|mred])).
      disc_rule_conds.

      + specialize (H1 nost2 porq1 (porq1 +[downRq <- rqi2]) nil).
        rewrite H7, Heqrtrs1 in H1; simpl in H1; inv H1.
        specialize (H4 nost2 porq1 (porq1 +[upRq <- rqi]) nil).
        rewrite Heqtrs2, Heqrtrs2 in H4; simpl in H4; inv H4.
        repeat split.
        * eapply H13; [eassumption|mred].
        * f_equal; meq.
          { destruct rqi1 as [rqim1 rss1 rsb1].
            destruct rqi2 as [rqim2 rss2 rsb2].
            simpl in *; subst.
            destruct Hrrs as [? _].
            erewrite footprintUpDownOk_rs_eq_rss
              with (rssFrom1:= rss1) (rssFrom2:= rss2); eauto.
          }
          { destruct rqi as [rqim rss rsb].
            destruct rqi0 as [rqim0 rss0 rsb0].
            simpl in *; subst.
            destruct Hrrs as [? _].
            pose proof (footprintUpOk_rs_None_eq H52 H58); dest; subst.
            reflexivity.
          }
      
      + specialize (H1 nost2 porq1 (porq1 +[downRq <- rqi2]) nil).
        rewrite H7, Heqrtrs1 in H1; simpl in H1; inv H1.
        specialize (H4 nost2 porq1 (porq1 +[upRq <- rqi]) [(rqFrom, rqfm)]).
        rewrite Heqtrs2, Heqrtrs2 in H4; simpl in H4; inv H4.
        repeat split.
        * eapply H13; [eassumption|mred].
        * f_equal; meq.
          { destruct rqi1 as [rqim1 rss1 rsb1].
            destruct rqi2 as [rqim2 rss2 rsb2].
            simpl in *; subst.
            destruct Hrrs as [? _].
            erewrite footprintUpDownOk_rs_eq_rss
              with (rssFrom1:= rss1) (rssFrom2:= rss2); eauto.
            erewrite footprintUpDownOk_rs_eq_back
              with (rsbTo1:= rsbTo) (rsbTo2:= rsbTo0); eauto.
          }
          { destruct rqi as [rqim rss rsb].
            destruct rqi0 as [rqim0 rss0 rsb0].
            simpl in *; subst.
            destruct Hrrs as [? _].
            pose proof (footprintUpOk_rs_None_eq H52 H58); dest; subst.
            reflexivity.
          }

      + specialize (H1 nost2 porq1 (porq1 +[downRq <- rqi2]) [(rqFrom, rqfm)]).
        rewrite H7, Heqrtrs1 in H1; simpl in H1; inv H1.
        specialize (H4 nost2 porq1 (porq1 +[upRq <- rqi]) nil).
        rewrite Heqtrs2, Heqrtrs2 in H4; simpl in H4; inv H4.
        repeat split.
        * eapply H13; [eassumption|mred].
        * f_equal; meq.
          { destruct rqi1 as [rqim1 rss1 rsb1].
            destruct rqi2 as [rqim2 rss2 rsb2].
            simpl in *; subst.
            destruct Hrrs as [? _].
            erewrite footprintUpDownOk_rs_eq_rss
              with (rssFrom1:= rss1) (rssFrom2:= rss2); eauto.
          }
          { destruct rqi as [rqim rss rsb].
            destruct rqi0 as [rqim0 rss0 rsb0].
            simpl in *; subst.
            destruct Hrrs as [? _].
            pose proof (footprintUpOk_rs_Some_eq H0 H52 H58); dest; subst.
            reflexivity.
          }
        
      + specialize (H1 nost2 porq1 (porq1 +[downRq <- rqi2]) [(rqFrom, rqfm)]).
        rewrite H7, Heqrtrs1 in H1; simpl in H1; inv H1.
        specialize (H4 nost2 porq1 (porq1 +[upRq <- rqi]) [(rqFrom1, rqfm1)]).
        rewrite Heqtrs2, Heqrtrs2 in H4; simpl in H4; inv H4.
        repeat split.
        * eapply H13; [eassumption|mred].
        * f_equal; meq.
          { destruct rqi1 as [rqim1 rss1 rsb1].
            destruct rqi2 as [rqim2 rss2 rsb2].
            simpl in *; subst.
            destruct Hrrs as [? _].
            erewrite footprintUpDownOk_rs_eq_rss
              with (rssFrom1:= rss1) (rssFrom2:= rss2); eauto.
            erewrite footprintUpDownOk_rs_eq_back
              with (rsbTo3:= rsbTo1) (rsbTo4:= rsbTo2); eauto.
          }
          { destruct rqi as [rqim rss rsb].
            destruct rqi0 as [rqim0 rss0 rsb0].
            simpl in *; subst.
            destruct Hrrs as [? _].
            pose proof (footprintUpOk_rs_Some_eq H0 H52 H58); dest; subst.
            reflexivity.
          }
  Qed.

  Lemma rqUpUp_rqDownDown_reducible:
    forall oidx (rule1 rule2: Rule),
      RqUpUp dtr oidx rule1 ->
      StateSilent rule1 -> MsgOutsOrthORq rule1 ->
      RqDownDown dtr oidx rule2 ->
      StateSilent rule2 -> MsgOutsOrthORq rule2 ->
      NonConflictingR (oinvs oidx) rule1 rule2.
  Proof.
    intros.
    red; intros.
    split.
    - disc_rule_conds.
      + eapply H14; [eassumption|mred].
      + eapply H14; [eassumption|mred].
    - remember (rule_trs rule2 nost1 norq1 ins2) as trs2.
      destruct trs2 as [[nost2 norq2] outs2]; apply eq_sym in Heqtrs2.
      remember (rule_trs rule2 post1 porq1 ins2) as rtrs2.
      destruct rtrs2 as [[rnost2 rnorq2] routs2]; apply eq_sym in Heqrtrs2.
      remember (rule_trs rule1 rnost2 rnorq2 ins1) as rtrs1.
      destruct rtrs1 as [[rnost1 rnorq1] routs1]; apply eq_sym in Heqrtrs1.

      assert (rule_precond rule2 post1 porq1 ins2)
        by (disc_rule_conds; try (eapply H14; [eassumption|mred])).
      assert (rule_precond rule1 rnost2 rnorq2 ins1)
        by (disc_rule_conds; try (eapply H12; [eassumption|mred])).
      disc_rule_conds.

      + specialize (H1 nost2 porq1 (porq1 +[downRq <- rqi2]) nil).
        rewrite H7, Heqrtrs1 in H1; simpl in H1; inv H1.
        specialize (H4 nost2 porq1 (porq1 +[upRq <- rqi]) [(rqFrom, rqfm)]).
        rewrite Heqtrs2, Heqrtrs2 in H4; simpl in H4; inv H4.
        repeat split.
        * eapply H13; [eassumption|mred].
        * f_equal; meq.
          { destruct rqi1 as [rqim1 rss1 rsb1].
            destruct rqi2 as [rqim2 rss2 rsb2].
            simpl in *; subst.
            destruct Hrrs as [? _].
            pose proof (footprintDownDownOk_rs_eq H0 H62 H68); dest; subst.
            reflexivity.
          }
          { destruct rqi as [rqim rss rsb].
            destruct rqi0 as [rqim0 rss0 rsb0].
            simpl in *; subst.
            destruct Hrrs as [? _].
            pose proof (footprintUpOk_rs_None_eq H52 H58); dest; subst.
            reflexivity.
          }

      + specialize (H1 nost2 porq1 (porq1 +[downRq <- rqi2]) [(rqFrom, rqfm)]).
        rewrite H7, Heqrtrs1 in H1; simpl in H1; inv H1.
        specialize (H4 nost2 porq1 (porq1 +[upRq <- rqi]) [(rqFrom1, rqfm1)]).
        rewrite Heqtrs2, Heqrtrs2 in H4; simpl in H4; inv H4.
        repeat split.
        * eapply H13; [eassumption|mred].
        * f_equal; meq.
          { destruct rqi1 as [rqim1 rss1 rsb1].
            destruct rqi2 as [rqim2 rss2 rsb2].
            simpl in *; subst.
            destruct Hrrs as [? _].
            pose proof (footprintDownDownOk_rs_eq H0 H62 H68); dest; subst.
            reflexivity.
          }
          { destruct rqi as [rqim rss rsb].
            destruct rqi0 as [rqim0 rss0 rsb0].
            simpl in *; subst.
            destruct Hrrs as [? _].
            pose proof (footprintUpOk_rs_Some_eq H0 H52 H58); dest; subst.
            reflexivity.
          }
  Qed.

  Ltac disc_rule_custom ::=
    try disc_lock_conds;
    try disc_footprints_ok;
    try disc_messages_in;
    try disc_rqToUpRule.

  Lemma rqUp_lbl_commutes:
    forall oidxTo rqUps (Hru: rqUps <> nil)
           st1 st2 oidx1 ridx1 rins1 routs1 oidx2 ridx2 rins2 routs2,
      RqUpMsgs dtr oidxTo rqUps ->
      SubList rqUps routs1 ->
      DisjList routs1 rins2 ->
      Reachable (steps step_m) sys st1 ->
      steps step_m sys st1
            [RlblInt oidx2 ridx2 rins2 routs2;
               RlblInt oidx1 ridx1 rins1 routs1] st2 ->
      NonConflictingL sys oinvs oidx1 ridx1 oidx2 ridx2 /\
      DisjList (idsOf rins1) (idsOf rins2) /\
      DisjList routs1 rins2 /\
      DisjList (idsOf routs1) (idsOf routs2).
  Proof.
    intros; destruct Hrrs as [? [? [? _]]].
    
    (* Register necessary invariants. *)
    inv H3.
    pose proof (upLockInv_ok Hiorqs H5 H4 (reachable_steps H2 H10)) as HlockInv.
    pose proof (footprints_ok Hiorqs H5 (reachable_steps H2 H10)) as HftInv.
    
    inv_steps.
    pose proof (rqUp_spec Hru H H0 H2 H13).
    destruct H3 as [? [? [? [? ?]]]].
    destruct H9 as [orq [rqiu [? [? ?]]]].
    destruct H10 as [rqTo [rqtm [? [? ?]]]].
    subst.
    inv_step; simpl in *.
    good_rqrs_rule_get rule.
    eapply rqUpMsgs_RqToUpRule in H8; try eassumption.
    good_rqrs_rule_get rule0.

    destruct (idx_dec (obj_idx obj) (obj_idx obj0)); subst.
    - red_obj_rule; rename obj0 into obj.
      good_rqrs_rule_cases rule0.

      + (** case [ImmDownRule] *)
        exfalso; disc_rule_conds.

      + (** case [ImmUpRule] *)
        assert (RsToUpRule dtr (obj_idx obj) rule0) by (left; assumption).
        good_rqUp_rsUp_get rule rule0.
        phide H3; phide H8.
        repeat split; try assumption.
        * right; split; [reflexivity|].
          intros; red_obj_rule.
          assumption.
        * destruct H14; dest; subst; disc_rule_conds.
          { apply DisjList_nil_1. }
          { solve_midx_disj. }
        * disc_rule_conds; solve_midx_disj.

      + (** case [RqFwdRule] *)
        mred.
        destruct H10; destruct H10 as [|[|]].
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
          { destruct H14; dest; subst; [apply DisjList_nil_1|].
            disc_rule_conds; [apply DisjList_nil_2|].
            destruct (idx_dec upCObj.(obj_idx) cidx0); subst.
            { exfalso.
              good_locking_get upCObj.
              red in H.
              apply parentIdxOf_not_eq in H10;
                [|destruct Hrrs as [[? ?] _]; assumption]; mred.
              match goal with
              | [H: match ?ul with | Some _ => _ | None => _ end |- _] =>
                destruct ul
              end.
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
          { phide H3; phide H8.
            disc_rule_conds; solve_midx_disj.
          }
          
        * (** case [RqDownDown] *)
          repeat split; try assumption.
          { right; split; [reflexivity|].
            intros; red_obj_rule.
            destruct H8.
            red in H8, H9; dest.
            eapply rqUpUp_rqDownDown_reducible; eauto.
          }
          { phide H3; phide H8.
            destruct H14; dest; subst.
            { apply DisjList_nil_1. }
            { disc_rule_conds; solve_midx_disj. }
          }
          { phide H3; phide H8.
            disc_rule_conds; solve_midx_disj.
          }

      + (** case [RsBackRule] *)
        good_footprint_get (obj_idx obj).
        destruct H10; destruct H10; dest.
        * (** case [FootprintReleasingUp] *)
          phide H3; phide H8.
          exfalso; disc_rule_conds.
          { good_locking_get obj.
            disc_lock_conds; dest.
            eapply upLockedInv_False_1; eauto.
            { apply InMP_or_enqMP; auto. }
            { apply FirstMP_InMP; auto. }
          }
          { good_locking_get obj.
            disc_lock_conds; dest.
            eapply upLockedInv_False_1; eauto.
            { apply InMP_or_enqMP; auto. }
            { apply FirstMP_InMP; auto. }
          }

        * (** case [FootprintReleasingDown] *)
          assert (RsToUpRule dtr (obj_idx obj) rule0) by (right; eauto).
          good_rqUp_rsUp_get rule rule0.
          phide H3; phide H8.
          disc_rule_conds.
          { repeat split; try assumption.
            { right; split; [reflexivity|].
              intros; red_obj_rule.
              assumption.
            }
            { destruct H14; dest; subst; [apply DisjList_nil_1|].
              disc_rule_conds.
              rewrite H47; solve_midx_disj.
            }
            { solve_midx_disj. }
          }
          { repeat split; try assumption.
            { right; split; [reflexivity|].
              intros; red_obj_rule.
              assumption.
            }
            { destruct H14; dest; subst; [apply DisjList_nil_1|].
              disc_rule_conds.
              rewrite H47; solve_midx_disj.
            }
            { solve_midx_disj. }
          }

      + (** case [RsDownRqDownRule] *)
        phide H3; phide H8.
        good_footprint_get (obj_idx obj).
        disc_rule_conds.
        exfalso.
        good_locking_get obj.
        disc_lock_conds; dest.
        eapply upLockedInv_False_1; eauto.
        { apply InMP_or_enqMP; auto. }
        { apply FirstMP_InMP; auto. }

    - (* Better to extract as a lemma for arbitrary [Rule]s? *)
      split; [red; auto|].
      destruct H14; dest; subst; disc_rule_conds.
        
      + good_footprint_get (obj_idx obj0).
        good_rqrs_rule_cases rule0.
        * disc_rule_conds; [repeat ssplit; apply DisjList_nil_2|].
          repeat ssplit; [apply DisjList_nil_1|assumption|solve_midx_disj].
        * disc_rule_conds.
          repeat ssplit; [apply DisjList_nil_1|assumption|solve_midx_disj].
        * disc_rule_conds.
          { repeat ssplit; try apply DisjList_nil_2.
            solve_midx_disj.
          }
          all: repeat ssplit; try apply DisjList_nil_1; [assumption|solve_midx_disj].
        * disc_rule_conds.
          { repeat ssplit; [apply DisjList_nil_1|assumption|solve_midx_disj]. }
          { repeat ssplit; [apply DisjList_nil_1|assumption|apply DisjList_nil_2]. }
          { rewrite H50.
            repeat ssplit; [apply DisjList_nil_1|assumption|solve_midx_disj]. }
          { rewrite H50.
            repeat ssplit; [apply DisjList_nil_1|assumption|solve_midx_disj]. }
        * disc_rule_conds.
          repeat ssplit; [apply DisjList_nil_1|assumption|solve_midx_disj].

      + good_footprint_get (obj_idx obj0).
        good_rqrs_rule_cases rule0.
        * disc_rule_conds; [repeat ssplit; apply DisjList_nil_2|].
          destruct (idx_dec cidx0 cidx).
          { subst; rewrite H63 in H12; elim n; inv H12; reflexivity. }
          { split; [|split]; [|assumption|]; solve_midx_disj. }
        * disc_rule_conds.
          split; [|split]; [|assumption|]; solve_midx_disj.
        * disc_rule_conds.
          { repeat ssplit; try apply DisjList_nil_2.
            solve_midx_disj.
          }
          { destruct (idx_dec cidx cidx0).
            { subst; rewrite H7 in H12; elim n; inv H12; reflexivity. }
            { split; [|split]; [|assumption|]; solve_midx_disj. }
          }
          { split; [|split]; try apply DisjList_nil_2; solve_midx_disj. }
          { destruct (idx_dec cidx0 (obj_idx upCObj)).
            { subst; rewrite H10 in H12; elim n; inv H12; reflexivity. }
            { split; [|split]; [|assumption|]; solve_midx_disj. }
          }
          { split; [|split]; [|assumption|]; solve_midx_disj. }
        * disc_rule_conds.
          { split; [|split]; [|assumption|]; solve_midx_disj. }
          { split; [|split]; [solve_midx_disj|assumption|apply DisjList_nil_2]. }
          { rewrite H55.
            split; [|split]; [|assumption|]; solve_midx_disj. }
          { rewrite H55.
            split; [|split]; [|assumption|]; solve_midx_disj. }
        * disc_rule_conds.
          split; [|split]; [|assumption|]; solve_midx_disj.
  Qed.

  Hypothesis (Hoinvs: InvReachable sys step_m (liftObjInvs oinvs)).
  
  Lemma rqUp_lbl_reducible:
    forall oidxTo rqUps oidx1 ridx1 rins1 routs1,
      rqUps <> nil ->
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
    eapply internal_steps_commutes; eauto.
    intros; eapply rqUp_lbl_commutes; eauto.
  Qed.

  Definition RqUpMsgsFrom (ruFrom ruTo: IdxT) (msgs: list (Id Msg)) :=
    exists rqUp,
      msgs = [rqUp] /\
      msg_type (valOf rqUp) = MRq /\
      parentIdxOf dtr ruFrom = Some ruTo /\
      rqEdgeUpFrom dtr ruFrom = Some (idOf rqUp).

  Lemma rqUpMsgsFrom_RqUpMsgs:
    forall cidx pidx rqTo rqtm,
      RqUpMsgs dtr pidx [(rqTo, rqtm)] ->
      parentIdxOf dtr cidx = Some pidx ->
      rqEdgeUpFrom dtr cidx = Some rqTo ->
      RqUpMsgsFrom cidx pidx [(rqTo, rqtm)].
  Proof.
    intros.
    destruct H; [discriminate|].
    destruct H as [rcidx [rqUp ?]]; dest; subst.
    inv H; simpl in *.
    econstructor; eauto.
  Qed.

  Lemma rqUpMsgs_RqUpMsgsFrom:
    forall cidx pidx msgs,
      RqUpMsgsFrom cidx pidx msgs ->
      RqUpMsgs dtr pidx msgs.
  Proof.
    intros.
    destruct H as [rqUp ?]; dest; subst.
    right; do 2 eexists; eauto.
  Qed.

  Inductive RqUpHistory: History -> IdxT -> list (Id Msg) -> Prop :=
  | RqUpIntro:
      forall oidx ridx rins routs oidxTo,
        RqUpMsgsFrom oidx oidxTo routs ->
        RqUpHistory [RlblInt oidx ridx rins routs] oidxTo routs
  | RqUpCont:
      forall phst pouts oidx ridx rins routs oidxTo,
        RqUpHistory phst oidx pouts ->
        rins = pouts ->
        RqUpMsgsFrom oidx oidxTo routs ->
        RqUpHistory (RlblInt oidx ridx rins routs :: phst) oidxTo routs.

  Lemma rqUpHistory_RqUpMsgsFrom:
    forall hst oidx rqUps,
      RqUpHistory hst oidx rqUps ->
      exists cidx, RqUpMsgsFrom cidx oidx rqUps.
  Proof.
    destruct 1; simpl; intros; eauto.
  Qed.
  
  Lemma rqUp_atomic:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      forall oidxTo rqUps (Hru: rqUps <> nil),
        RqUpMsgs dtr oidxTo rqUps ->
        SubList rqUps eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          steps step_m sys st1 hst st2 ->
          eouts = rqUps /\ RqUpHistory hst oidxTo eouts.
  Proof.
    induction 1; simpl; intros; subst.
    - inv_steps.
      eapply rqUp_spec in H8; try eassumption.
      destruct H8 as [? [? [? [? ?]]]].
      destruct H5 as [orq [rqiu [? [? ?]]]].
      destruct H6 as [rqTo [rqtm ?]]; dest; subst.
      split; [reflexivity|].
      econstructor.
      eapply rqUpMsgsFrom_RqUpMsgs; eauto.
    - destruct H5; [exfalso; auto|].
      destruct H2 as [cidx [rqUp ?]]; dest; subst.
      inv_steps.
      apply SubList_singleton_In in H6.
      apply in_app_or in H6; destruct H6.
      + exfalso.
        pose proof (removeL_In_2 _ _ _ _ H2).
        assert (RqUpMsgs dtr oidxTo [rqUp] /\ SubList [rqUp] eouts).
        { split.
          { right; exists cidx, rqUp; repeat split; assumption. }
          { red; intros; dest_in; assumption. }
        }
        dest.
        specialize (IHAtomic _ _ Hru H8 H9 _ _ H7 H11); dest.
        assert (exists oidxTo, RqUpMsgs dtr oidxTo eouts)
          by (inv H12; eauto).
        destruct H14 as [poidxTo ?].
        destruct H14; [subst; discriminate|].
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
          dest_in.
          elim H4; simpl; tauto.
      + assert (RqUpMsgs dtr oidxTo [rqUp] /\ SubList [rqUp] routs).
        { split.
          { right; exists cidx, rqUp; repeat split; assumption. }
          { red; intros; dest_in; assumption. }
        }
        dest.
        eapply rqUp_spec in H13; eauto.
        destruct H13 as [? [? [? [? ?]]]].
        destruct H13 as [orq [rqiu [? [? ?]]]].
        destruct H14 as [rqTo [rqtm ?]]; dest; subst.
        assert ([rqUp] <> nil) as HrqUp by discriminate.
        specialize (IHAtomic _ _ H0 H9 H1 _ _ H7 H11); dest; subst.
        rewrite removeL_nil; simpl.
        split; [reflexivity|].
        econstructor; eauto.
        inv H14.
        eapply rqUpMsgsFrom_RqUpMsgs; eauto.
  Qed.

  Lemma rqUpHistory_lastOIdxOf:
    forall hst roidx rqUps rqUp,
      rqUps = [rqUp] ->
      RqUpHistory hst roidx rqUps ->
      forall loidx,
        lastOIdxOf hst = Some loidx ->
        parentIdxOf dtr loidx = Some roidx /\
        rqEdgeUpFrom dtr loidx = Some (idOf rqUp).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    inv H3; simpl in *.
    - inv H4.
      destruct H5 as [rqUp0 ?].
      dest; subst; inv H2.
      repeat disc_rule_minds.
      split; assumption.
    - inv H4.
      destruct H7 as [rqUp0 ?].
      dest; subst; inv H2.
      repeat disc_rule_minds.
      split; assumption.
  Qed.
  
  Lemma rqUp_atomic_lastOIdxOf:
    forall inits ins hst outs rqUp,
      Atomic inits ins hst outs [rqUp] ->
      forall st1 st2,
        Reachable (steps step_m) sys st1 ->
        steps step_m sys st1 hst st2 ->
        forall roidx loidx,
          RqUpMsgs dtr roidx [rqUp] ->
          lastOIdxOf hst = Some loidx ->
          parentIdxOf dtr loidx = Some roidx /\
          rqEdgeUpFrom dtr loidx = Some (idOf rqUp).
  Proof.
    intros.
    eapply rqUp_atomic in H; eauto;
      [dest|discriminate|apply SubList_refl].
    eapply rqUpHistory_lastOIdxOf; eauto.
  Qed.

  Lemma rqUpHistory_bounded:
    forall hst roidx rqUps,
      RqUpHistory hst roidx rqUps ->
      forall rqUp,
        rqUps = [rqUp] ->
        forall rcidx,
          parentIdxOf dtr rcidx = Some roidx ->
          rqEdgeUpFrom dtr rcidx = Some (idOf rqUp) ->
          forall tidx,
            In rcidx (subtreeIndsOf dtr tidx) ->
            SubList (oindsOf hst) (subtreeIndsOf dtr tidx).
  Proof.
    destruct Hrrs as [? [? ?]]; induction 1; simpl; intros; subst.
    - destruct H2 as [rqUp0 ?]; dest; subst.
      inv H2; repeat disc_rule_minds.
      apply SubList_cons; [|apply SubList_nil].
      assumption.
    - destruct H4 as [rqUp0 ?]; dest.
      inv H3; repeat disc_rule_minds.
      apply SubList_cons; [assumption|].

      clear -Hrrs H2 H8 IHRqUpHistory.
      pose proof (rqUpHistory_RqUpMsgsFrom H2).
      destruct H as [cidx [rqUp ?]]; dest; subst.
      eapply IHRqUpHistory; eauto.
      eapply inside_child_in; try apply Hrrs; eassumption.
  Qed.
  
  Lemma rqUp_atomic_bounded:
    forall rcidx roidx rqUp,
      parentIdxOf dtr rcidx = Some roidx ->
      rqEdgeUpFrom dtr rcidx = Some (idOf rqUp) ->
      RqUpMsgs dtr roidx [rqUp] ->
      forall inits ins hst outs,
        Atomic inits ins hst outs [rqUp] ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          steps step_m sys st1 hst st2 ->
        forall tidx,
          In rcidx (subtreeIndsOf dtr tidx) ->
          SubList (oindsOf hst) (subtreeIndsOf dtr tidx).
  Proof.
    intros.
    eapply rqUp_atomic in H2; eauto; [dest|discriminate|apply SubList_refl].
    eapply rqUpHistory_bounded; eauto.
  Qed.

  Corollary rqUp_atomic_inside_tree:
    forall roidx rqUps,
      rqUps <> nil ->
      RqUpMsgs dtr roidx rqUps ->
      forall inits ins hst outs,
        Atomic inits ins hst outs rqUps ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          steps step_m sys st1 hst st2 ->
          SubList (oindsOf hst) (subtreeIndsOf dtr roidx).
  Proof.
    intros.
    pose proof H0.
    destruct H4; [exfalso; auto|].
    destruct H4 as [cidx [rqUp ?]]; dest; subst.
    eapply rqUp_atomic_bounded; eauto.
    apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
  Qed.

  Lemma rqUp_ins_disj:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall cidx corq pidx porq rqUp down prqi,
        parentIdxOf dtr cidx = Some pidx ->
        rqEdgeUpFrom dtr cidx = Some rqUp ->
        edgeDownTo dtr cidx = Some down ->
        st1.(st_orqs)@[cidx] = Some corq -> corq@[upRq] <> None ->
        st1.(st_orqs)@[pidx] = Some porq ->
        porq@[upRq] = Some prqi -> prqi.(rqi_midx_rsb) = Some down ->
        forall oidx ridx rins routs st2,
          step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
          DisjList (idsOf rins) [rqUp].
  Proof.
    intros; destruct Hrrs as [? [? ?]].

    pose proof (footprints_ok Hiorqs H10 H) as HftInv.
    inv_step; simpl in *.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - (** case [ImmDownRule] *)
      disc_rule_conds; [apply DisjList_nil_1|].
      destruct (idx_dec cidx0 cidx);
        subst; [|solve_midx_disj].
      exfalso.
      rewrite H2 in H39; inv H39.
      congruence.

    - (** case [ImmUpRule] *)
      disc_rule_conds.
      solve_midx_disj.

    - (** case [RqFwdRule] *)
      disc_rule_conds.
      + (** case [RqUpUp-silent] *)
        apply DisjList_nil_1.
      + (** case [RqUpUp] *)
        destruct (idx_dec cidx0 cidx);
          subst; [|solve_midx_disj].
        rewrite H0 in H8; inv H8.
        congruence.
      + (** case [RqUpDown-silent] *)
        apply DisjList_nil_1.
      + (** case [RqUpDown] *)
        pose proof (upLockInv_ok Hiorqs H10 H9 H) as HlockInv.
        good_locking_get upCObj.
        destruct (idx_dec (obj_idx upCObj) cidx);
          subst; [|solve_midx_disj].
        exfalso.
        rewrite H0 in H13; inv H13.
        rewrite H1 in H14; inv H14.
        red in H12; rewrite H3 in H12; simpl in H12.
        destruct (corq@[upRq]); [|elim H4; reflexivity].
        dest; destruct H13 as [rqUp [rdown [pidx ?]]]; dest.
        disc_rule_conds.
        eapply xor3_False_2; [eassumption| |].
        * eapply findQ_length_one; eauto.
        * red.
          rewrite H5; simpl.
          exists prqi; auto.
      + (** case [RqDownDown] *)
        solve_midx_disj.

    - (** case [RsBackRule] *)
      good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + solve_midx_disj.
      + solve_midx_disj.
      + rewrite H36; solve_midx_disj.
      + rewrite H36; solve_midx_disj.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      solve_midx_disj.
  Qed.

  Lemma rqUpHistory_lpush_lbl:
    forall phst oidxTo rqUps,
      RqUpHistory phst oidxTo rqUps ->
      forall oidx ridx rins routs,
        DisjList rqUps rins ->
        forall st1,
          Reachable (steps step_m) sys st1 ->
          forall st2,
            steps step_m sys st1 (RlblInt oidx ridx rins routs :: phst) st2 ->
            steps step_m sys st1 (phst ++ [RlblInt oidx ridx rins routs]) st2.
  Proof.
    induction 1; simpl; intros; subst.
    - eapply rqUp_lbl_reducible; eauto;
        [|eapply rqUpMsgs_RqUpMsgsFrom; eauto
         |apply SubList_refl].
      red in H; dest; subst; discriminate.
    - eapply reducible_trans; eauto.
      + apply reducible_cons_2.
        eapply rqUp_lbl_reducible; eauto;
          [|eapply rqUpMsgs_RqUpMsgsFrom; eauto
           |apply SubList_refl].
        red in H1; dest; subst; discriminate.
      + destruct Hrrs as [? [? ?]].
        apply reducible_cons.
        red; intros.
        eapply IHRqUpHistory; eauto.

        assert (exists coidx cridx crins pphst coidxTo,
                   phst = RlblInt coidx cridx crins pouts :: pphst /\
                   RqUpMsgs dtr coidxTo pouts).
        { inv H.
          { do 5 eexists; split; eauto; eapply rqUpMsgs_RqUpMsgsFrom; eauto. }
          { do 5 eexists; split; eauto; eapply rqUpMsgs_RqUpMsgsFrom; eauto. }
        }
        destruct H8 as [coidx [cridx [crins [pphst [coidxTo ?]]]]]; dest; subst.
        clear H7; inv_steps.

        assert (Reachable (steps step_m) sys st7).
        { eapply reachable_steps; [apply H3|eassumption]. }

        pose proof H14 as Hru.
        eapply rqUp_spec with (rqUps:= routs) in Hru; eauto;
          [|red in H1; dest; subst; discriminate
           |eapply rqUpMsgs_RqUpMsgsFrom; eauto
           |apply SubList_refl
           |eapply reachable_steps;
            [eapply H4|apply steps_singleton; eassumption]].
        destruct Hru as [? [? [? [? ?]]]].
        destruct H12 as [orq [rqiu ?]].
        destruct H16 as [rqTo [rqtm ?]]; dest; subst.

        destruct H20.
        1: {
          exfalso; dest; subst.
          apply rqUpHistory_RqUpMsgsFrom in H; destruct H as [cidx ?].
          red in H; dest; discriminate.
        }
        destruct H16 as [cidx [rqFrom [rqfm [down ?]]]]; dest; subst.

        pose proof H15 as Hru.
        eapply rqUp_spec with (rqUps:= [(rqFrom, rqfm)]) in Hru; eauto;
          [|discriminate|apply SubList_refl].
        destruct Hru as [? [? [? [? ?]]]].
        destruct H26 as [corq [crqiu ?]].
        destruct H27 as [crqTo [crqtm ?]]; dest; subst.
        inv H27.

        phide H16; disc_rule_conds; try discriminate.
        apply DisjList_comm, idsOf_DisjList; simpl.
        eapply rqUp_ins_disj.
        * instantiate (1:= st5).
          eapply reachable_steps; [|apply steps_singleton; eassumption].
          eapply reachable_steps; [|apply steps_singleton; eassumption].
          assumption.
        * apply H25.
        * assumption.
        * eassumption.
        * instantiate (1:= corq).
          apply parentIdxOf_not_eq in H25;
            [|destruct Hrrs as [[? ?]]; assumption].
          clear H13 H15.
          inv_step; simpl in *.
          mred.
        * congruence.
        * instantiate (1:= orq); assumption.
        * eassumption.
        * assumption.
        * eassumption.
  Qed.
  
  Lemma rqUp_outs_disj:
    forall oidxTo rqUp st1 st2 oidx ridx rins routs,
      RqUpMsgs dtr oidxTo [rqUp] ->
      Reachable (steps step_m) sys st1 ->
      InMPI st1.(st_msgs) rqUp ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      DisjList routs [rqUp].
  Proof.
    intros; destruct Hrrs as [? [? ?]].
    pose proof (footprints_ok Hiorqs H4 H0).
    pose proof (upLockInv_ok Hiorqs H4 H3 H0).

    destruct H; [discriminate|].
    destruct H as [ruIdx [[rqUp' rqm] ?]]; dest.
    inv H; rename rqUp' into rqUp; simpl in *.
    apply idsOf_DisjList; simpl.
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds; solve_midx_disj.
      intro; dest_in.
    - disc_rule_conds; solve_midx_disj.

    - good_locking_get obj.
      disc_rule_conds.
      + destruct (idx_dec ruIdx (obj_idx obj)); subst; [|solve_midx_disj].
        exfalso.
        destruct H2; [congruence|].
        destruct H2 as [orqUp [down [pidx ?]]]; dest.
        disc_rule_conds.
        eapply InMP_findQ_False; eauto.
      + destruct (idx_dec ruIdx (obj_idx obj)); subst; [|solve_midx_disj].
        exfalso.
        destruct H2; [congruence|].
        destruct H2 as [orqUp [down [pidx ?]]]; dest.
        disc_rule_conds.
        eapply InMP_findQ_False; eauto.
      + solve_midx_disj.
      + solve_midx_disj.
      + solve_midx_disj.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds; solve_midx_disj.
      intro; dest_in.
    - disc_rule_conds; solve_midx_disj.
  Qed.

  Lemma rqUpHistory_outs:
    forall hst oidxTo outs,
      RqUpHistory hst oidxTo outs ->
      forall rqUp st1 st2,
        outs = [rqUp] ->
        steps step_m sys st1 hst st2 ->
        InMPI st2.(st_msgs) rqUp.
  Proof.
    induction 1; simpl; intros; subst.
    - inv_steps; inv_step.
      destruct rqUp as [ruIdx rqm]; simpl in *.
      apply InMP_or_enqMP; auto.
    - inv_steps; inv_step.
      destruct rqUp as [ruIdx rqm]; simpl in *.
      apply InMP_or_enqMP; auto.
  Qed.

  Lemma rqUpHistory_lpush_unit_reducible:
    forall phst oidxTo rqUps,
      RqUpMsgs dtr oidxTo rqUps ->
      RqUpHistory phst oidxTo rqUps ->
      forall inits ins hst outs eouts,
        Atomic inits ins hst outs eouts ->
        DisjList rqUps inits ->
        Reducible sys (hst ++ phst) (phst ++ hst).
  Proof.
    induction 3; simpl; intros; subst.
    - red; intros.
      eapply rqUpHistory_lpush_lbl; eauto.
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
        red; intros.
        eapply rqUpHistory_lpush_lbl; eauto.
        clear st0 Hr0 st3 H5.
        
        apply DisjList_comm.
        eapply DisjList_SubList; [eassumption|].
        inv_steps.
        clear H2 H3 H11 rins st2.
        eapply steps_split in H9; [|reflexivity].
        destruct H9 as [st2 [? ?]].

        assert (Reachable (steps step_m) sys st2)
          by (eapply reachable_steps; eauto).
        destruct H.
        1: {
          subst.
          apply rqUpHistory_RqUpMsgsFrom in H0.
          destruct H0 as [cidx ?]; red in H; dest; discriminate.
        }
        destruct H as [ruIdx [rqUp ?]]; dest; subst.
        eapply rqUpHistory_outs in H0; [|reflexivity|eassumption].

        clear H2 IHAtomic phst.
        generalize dependent st3.
        generalize dependent st2.
        induction H1; intros; subst.
        * inv_steps.
          eapply rqUp_outs_disj.
          { right; exists ruIdx, rqUp; repeat split; eauto. }
          { apply H4. }
          { assumption. }
          { eassumption. }
        * inv_steps.
          specialize (IHAtomic H7 _ H9 H10 _ H12).
          eapply atomic_messages_in_in in H10; eauto;
            [|eapply DisjList_In_2; [eassumption|left; reflexivity]].
          apply DisjList_app_4; [apply removeL_DisjList; assumption|].
          eapply rqUp_outs_disj.
          { right; exists ruIdx, rqUp; repeat split; eauto. }
          { eapply reachable_steps; eauto. }
          { assumption. }
          { eassumption. }
  Qed.    
  
  Lemma rqUp_lpush_unit_reducible:
    forall oidxTo rqUps inits ins hst outs eouts
           pinits pins phst pouts peouts,
      Atomic pinits pins phst pouts peouts ->
      rqUps <> nil -> RqUpMsgs dtr oidxTo rqUps ->
      SubList rqUps peouts ->
      Atomic inits ins hst outs eouts ->
      DisjList peouts inits ->
      Reducible sys (hst ++ phst) (phst ++ hst).
  Proof.
    intros; red; intros.
    eapply steps_split in H5; [|reflexivity].
    destruct H5 as [sti [? ?]].
    eapply rqUpHistory_lpush_unit_reducible; eauto.
    - eapply rqUp_atomic in H; eauto.
      dest; subst; assumption.
    - eapply DisjList_SubList; eassumption.
    - eapply steps_append; eauto.
  Qed.
  
End RqUpReduction.

Close Scope list.
Close Scope fmap.

