Require Import Peano_dec Omega List.
Require Import Common FMap IndexSupport.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.
Require Import RqRsInvMsg RqRsInvAtomic RqRsInvLock.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section InsideTree.
  Context `{oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System).

  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hrrs: RqRsSys dtr sys).

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try solve_midx_false.
  
  Lemma step_inside_tree_ins_disj_outs:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall oidx ridx rins routs st2,
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        forall toidx,
          In oidx (subtreeIndsOf dtr toidx) ->
          forall uoidx ups,
            Forall (fun up =>
                      rqEdgeUpFrom dtr uoidx = Some (idOf up) \/
                      rsEdgeUpFrom dtr uoidx = Some (idOf up)) ups ->
            (uoidx = toidx \/ ~ In uoidx (subtreeIndsOf dtr toidx)) ->
            DisjList ups rins.
  Proof.
    intros.
    destruct Hrrs as [? [? ?]].
    pose proof (footprints_ok Hiorqs H5 H).
    apply (DisjList_false_spec (id_dec msg_dec)); intros [up umsg] Hin1 Hin2.
    rewrite Forall_forall in H2.
    specialize (H2 _ Hin1); simpl in H2.
    
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - disc_rule_conds.
      destruct H2; disc_rule_conds.
      destruct H3; subst.
      + eapply parent_not_in_subtree; try apply Hrrs; eauto.
      + elim H2; eapply inside_child_in; try apply Hrrs; eauto.

    - disc_rule_conds.
      destruct H2; disc_rule_conds.

    - disc_rule_conds.
      + destruct H2; disc_rule_conds.
        destruct H3; subst.
        * eapply parent_not_in_subtree; try apply Hrrs; eauto.
        * elim H3; eapply inside_child_in; try apply Hrrs; eauto.
      + destruct H2; disc_rule_conds.
        destruct H3; subst.
        * eapply parent_not_in_subtree; try apply Hrrs; eauto.
        * elim H3; eapply inside_child_in; try apply Hrrs; eauto.
      + destruct H2; disc_rule_conds.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + destruct H2; disc_rule_conds.
      + destruct H2; disc_rule_conds.
      + rewrite <-H32 in H26.
        apply in_map with (f:= idOf) in Hin2; simpl in Hin2.
        eapply RqRsDownMatch_rs_rq in H26; [|eassumption].
        destruct H26 as [cidx [down ?]]; dest.
        destruct H2; disc_rule_conds.
        destruct H3; subst.
        * eapply parent_not_in_subtree; try apply Hrrs; eauto.
        * elim H3; eapply inside_child_in; try apply Hrrs; eauto.
      + rewrite <-H32 in H11.
        apply in_map with (f:= idOf) in Hin2; simpl in Hin2.
        eapply RqRsDownMatch_rs_rq in H11; [|eassumption].
        destruct H11 as [cidx [down ?]]; dest.
        destruct H2; disc_rule_conds.
        destruct H3; subst.
        * eapply parent_not_in_subtree; try apply Hrrs; eauto.
        * elim H3; eapply inside_child_in; try apply Hrrs; eauto.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      destruct H2; disc_rule_conds.
  Qed.

  Lemma atomic_inside_tree_ins_disj_outs:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall st1 st2,
        Reachable (steps step_m) sys st1 ->
        steps step_m sys st1 hst st2 ->
        forall toidx,
          SubList (oindsOf hst) (subtreeIndsOf dtr toidx) ->
          forall uoidx ups,
            Forall (fun up =>
                      rqEdgeUpFrom dtr uoidx = Some (idOf up) \/
                      rsEdgeUpFrom dtr uoidx = Some (idOf up)) ups ->
            (uoidx = toidx \/ ~ In uoidx (subtreeIndsOf dtr toidx)) ->
            DisjList ups ins.
  Proof.
    induction 1; simpl; intros; subst.
    - inv_steps.
      apply SubList_singleton_In in H1.
      eapply step_inside_tree_ins_disj_outs; eauto.
    - inv_steps.
      apply SubList_cons_inv in H7; dest.
      apply DisjList_comm, DisjList_app_4; apply DisjList_comm.
      + eauto.
      + eapply step_inside_tree_ins_disj_outs;
          try (eapply reachable_steps; eassumption); eauto.
  Qed.

  Corollary atomic_inside_tree_inits_disj_rqUps:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall st1 st2,
        Reachable (steps step_m) sys st1 ->
        steps step_m sys st1 hst st2 ->
        forall toidx,
          SubList (oindsOf hst) (subtreeIndsOf dtr toidx) ->
          forall rqFrom rqUps,
            Forall (fun up => rqEdgeUpFrom dtr rqFrom = Some (idOf up)) rqUps ->
            (rqFrom = toidx \/ ~ In rqFrom (subtreeIndsOf dtr toidx)) ->
            DisjList rqUps inits.
  Proof.
    intros.
    eapply DisjList_comm, DisjList_SubList;
      [eapply atomic_inits_in; eassumption|].
    apply DisjList_comm.
    eapply atomic_inside_tree_ins_disj_outs; try eassumption.
    eapply Forall_impl; [|eassumption].
    simpl; intros; auto.
  Qed.

End InsideTree.

Section RqRsRed.
  Context `{oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System).

  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hrrs: RqRsSys dtr sys).

  Lemma rqrs_lbl_ins_disj:
    forall st11 st21,
      Reachable (steps step_m) sys st11 ->
      Reachable (steps step_m) sys st21 ->
      forall oidx1 ridx1 rins1 routs1 st12
             oidx2 ridx2 rins2 routs2 st22,
        oidx1 <> oidx2 ->
        step_m sys st11 (RlblInt oidx1 ridx1 rins1 routs1) st12 ->
        step_m sys st21 (RlblInt oidx2 ridx2 rins2 routs2) st22 ->
        DisjList (idsOf rins1) (idsOf rins2).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    eapply messages_in_cases in H5; try eassumption.
    eapply messages_in_cases in H6; try eassumption.

    destruct H5 as [|[|[|]]]; destruct H6 as [|[|[|]]];
      repeat disc_messages_in;
      unfold idOf in *; simpl in *; solve_midx_disj;
        try (intro Hx; rewrite Forall_forall in H6; specialize (H6 _ Hx);
             destruct H6 as [rcidx ?]; dest;
             solve_midx_false; fail);
        try (intro Hx; dest_in; fail);
        try (apply DisjList_nil_1; fail);
        try (apply DisjList_nil_2; fail).
    - intro Hx; rewrite Hx in *; clear Hx.
      repeat disc_rule_minds; auto.
    - apply (DisjList_false_spec idx_dec); intros midx Hin1 Hin2.
      rewrite Forall_forall in H8; specialize (H8 _ Hin1).
      destruct H8 as [cidx1 ?]; dest.
      rewrite Forall_forall in H7; specialize (H7 _ Hin2).
      destruct H7 as [cidx2 ?]; dest.
      repeat disc_rule_minds; auto.
    - intro Hx; rewrite Forall_forall in H7; specialize (H7 _ Hx).
      destruct H7 as [rcidx ?]; dest.
      solve_midx_false.
    - intro Hx; rewrite Forall_forall in H7; specialize (H7 _ Hx).
      destruct H7 as [rcidx ?]; dest.
      solve_midx_false.
  Qed.

  Lemma rqrs_lbl_outs_disj:
    forall st11 st21,
      Reachable (steps step_m) sys st11 ->
      Reachable (steps step_m) sys st21 ->
      forall oidx1 ridx1 rins1 routs1 st12
             oidx2 ridx2 rins2 routs2 st22,
        oidx1 <> oidx2 ->
        step_m sys st11 (RlblInt oidx1 ridx1 rins1 routs1) st12 ->
        step_m sys st21 (RlblInt oidx2 ridx2 rins2 routs2) st22 ->
        DisjList (idsOf routs1) (idsOf routs2).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    eapply messages_out_cases in H5; try eassumption.
    eapply messages_out_cases in H6; try eassumption.

    destruct H5 as [|[|[|]]]; destruct H6 as [|[|[|]]];
      repeat disc_messages_out;
      unfold idOf in *; simpl in *; solve_midx_disj;
        try (intro Hx; rewrite Forall_forall in H7; specialize (H7 _ Hx);
             destruct H7 as [rcidx ?]; dest;
             (solve_midx_false || (repeat disc_rule_minds; auto)); fail);
        try (intro Hx; dest_in; fail);
        try (apply DisjList_nil_1; fail);
        try (apply DisjList_nil_2; fail).
    - intro Hx; rewrite Forall_forall in H6; specialize (H6 _ Hx).
      destruct H6 as [rcidx ?]; dest.
      solve_midx_false.
    - intro Hx; rewrite Forall_forall in H6; specialize (H6 _ Hx).
      destruct H6 as [rcidx ?]; dest.
      solve_midx_false.
    - apply (DisjList_false_spec idx_dec); intros midx Hin1 Hin2.
      rewrite Forall_forall in H8; specialize (H8 _ Hin1).
      destruct H8 as [cidx1 ?]; dest.
      rewrite Forall_forall in H7; specialize (H7 _ Hin2).
      destruct H7 as [cidx2 ?]; dest.
      repeat disc_rule_minds; auto.
    - intro Hx; rewrite Hx in *; clear Hx.
      repeat disc_rule_minds; auto.
  Qed.

  Lemma rqrs_lbl_atomic_ins_disj:
    forall inits1 ins1 hst1 outs1 eouts1,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      forall st11 st21,
        Reachable (steps step_m) sys st11 ->
        Reachable (steps step_m) sys st21 ->
        forall oidx2 ridx2 rins2 routs2 st12 st22,
          ~ In oidx2 (oindsOf hst1) ->
          steps step_m sys st11 hst1 st12 ->
          step_m sys st21 (RlblInt oidx2 ridx2 rins2 routs2) st22 ->
          DisjList (idsOf ins1) (idsOf rins2).
  Proof.
    induction 1; simpl; intros; subst.
    - inv_steps.
      eapply rqrs_lbl_ins_disj; [| | |eassumption|eassumption]; eauto.
    - inv_steps.
      rewrite idsOf_app.
      eapply DisjList_app_4; eauto.
      eapply rqrs_lbl_ins_disj; [| | |eassumption|eassumption]; eauto.
      eapply reachable_steps; [eapply H5|eassumption].
  Qed.

  Lemma rqrs_atomic_ins_disj:
    forall inits1 ins1 hst1 outs1 eouts1 inits2 ins2 hst2 outs2 eouts2,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
      DisjList (oindsOf hst1) (oindsOf hst2) ->
      forall st11 st21,
        Reachable (steps step_m) sys st11 ->
        Reachable (steps step_m) sys st21 ->
        forall st12 st22,
          steps step_m sys st11 hst1 st12 ->
          steps step_m sys st21 hst2 st22 ->
          DisjList (idsOf ins1) (idsOf ins2).
  Proof.
    induction 2; simpl; intros; subst.
    - inv_steps.
      eapply rqrs_lbl_atomic_ins_disj;
        [| | | |eassumption|eassumption]; eauto.
      specialize (H0 oidx); destruct H0; intuition.
    - inv_steps.
      apply DisjList_comm, DisjList_cons in H6; dest.
      apply DisjList_comm in H4.
      specialize (IHAtomic H4 _ _ H7 H8).
      rewrite idsOf_app.
      apply DisjList_comm, DisjList_app_4; apply DisjList_comm; eauto.
      eapply rqrs_lbl_atomic_ins_disj;
        [| | | |eapply H9|eapply H13]; eauto.
  Qed.
  
  Lemma rqrs_lbl_atomic_outs_disj:
    forall inits1 ins1 hst1 outs1 eouts1,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      forall st11 st21,
        Reachable (steps step_m) sys st11 ->
        Reachable (steps step_m) sys st21 ->
        forall oidx2 ridx2 rins2 routs2 st12 st22,
          ~ In oidx2 (oindsOf hst1) ->
          steps step_m sys st11 hst1 st12 ->
          step_m sys st21 (RlblInt oidx2 ridx2 rins2 routs2) st22 ->
          DisjList (idsOf outs1) (idsOf routs2).
  Proof.
    induction 1; simpl; intros; subst.
    - inv_steps.
      eapply rqrs_lbl_outs_disj; [| | |eassumption|eassumption]; eauto.
    - inv_steps.
      rewrite idsOf_app.
      eapply DisjList_app_4; eauto.
      eapply rqrs_lbl_outs_disj; [| | |eassumption|eassumption]; eauto.
      eapply reachable_steps; [eapply H5|eassumption].
  Qed.

  Lemma rqrs_atomic_outs_disj:
    forall inits1 ins1 hst1 outs1 eouts1 inits2 ins2 hst2 outs2 eouts2,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
      DisjList (oindsOf hst1) (oindsOf hst2) ->
      forall st11 st21,
        Reachable (steps step_m) sys st11 ->
        Reachable (steps step_m) sys st21 ->
        forall st12 st22,
          steps step_m sys st11 hst1 st12 ->
          steps step_m sys st21 hst2 st22 ->
          DisjList (idsOf outs1) (idsOf outs2).
  Proof.
    induction 2; simpl; intros; subst.
    - inv_steps.
      eapply rqrs_lbl_atomic_outs_disj;
        [| | | |eassumption|eassumption]; eauto.
      specialize (H0 oidx); destruct H0; intuition.
    - inv_steps.
      apply DisjList_comm, DisjList_cons in H6; dest.
      apply DisjList_comm in H4.
      specialize (IHAtomic H4 _ _ H7 H8).
      rewrite idsOf_app.
      apply DisjList_comm, DisjList_app_4; apply DisjList_comm; eauto.
      eapply rqrs_lbl_atomic_outs_disj;
        [| | | |eapply H9|eapply H13]; eauto.
  Qed.

  Lemma rqrs_atomic_eouts_ins_disj:
    forall inits1 ins1 hst1 outs1 eouts1 inits2 ins2 hst2 outs2 eouts2,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
      DisjList (oindsOf hst1) (oindsOf hst2) ->
      DisjList eouts1 inits2 ->
      forall st11 st21,
        Reachable (steps step_m) sys st11 ->
        Reachable (steps step_m) sys st21 ->
        forall st12 st22,
          steps step_m sys st11 hst1 st12 ->
          steps step_m sys st21 hst2 st22 ->
          DisjList eouts1 ins2.
  Proof.
    intros.
    apply DisjList_app_1 with (l3:= eouts2).
    eapply DisjList_comm, DisjList_SubList;
      [eapply atomic_messages_ins_outs; eassumption|].
    apply DisjList_app_4; [apply DisjList_comm; assumption|].
    eapply DisjList_comm, DisjList_SubList;
      [eapply atomic_eouts_in; eassumption|].
    apply idsOf_DisjList.
    eapply rqrs_atomic_outs_disj;
      [eassumption|eassumption| | | |eassumption|eassumption]; eauto.
  Qed.

  Lemma rqrs_atomic_outs_inits_disj:
    forall inits1 ins1 hst1 outs1 eouts1 inits2 ins2 hst2 outs2 eouts2,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
      DisjList (oindsOf hst1) (oindsOf hst2) ->
      DisjList eouts1 inits2 ->
      forall st11 st21,
        Reachable (steps step_m) sys st11 ->
        Reachable (steps step_m) sys st21 ->
        forall st12 st22,
          steps step_m sys st11 hst1 st12 ->
          steps step_m sys st21 hst2 st22 ->
          DisjList outs1 inits2.
  Proof.
    intros.
    apply DisjList_comm, DisjList_app_2 with (l2:= inits1).
    eapply DisjList_comm, DisjList_SubList;
      [eapply atomic_messages_ins_outs in H; destruct H; eassumption|].
    apply DisjList_app_4; [|assumption].
    eapply DisjList_comm, DisjList_SubList;
      [eapply atomic_inits_in; eassumption|].
    apply DisjList_comm.
    apply idsOf_DisjList.
    eapply rqrs_atomic_ins_disj;
      [eassumption|eassumption| | | |eassumption|eassumption]; eauto.
  Qed.

  Lemma rqrs_lbl_reducible':
    forall inits1 ins1 hst1 outs1 eouts1 lbl2 oidx2 ridx2 rins2 routs2,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      lbl2 = RlblInt oidx2 ridx2 rins2 routs2 ->
      ~ In oidx2 (oindsOf hst1) ->
      DisjList outs1 rins2 ->
      Reducible sys (lbl2 :: hst1) (hst1 ++ [lbl2]).
  Proof.
    unfold Reducible; induction 1; simpl; intros; subst.
    - apply internal_commutes; auto.
      + red; intuition.
      + inv_steps.
        eapply rqrs_lbl_ins_disj; [| | |eassumption|eassumption]; eauto.
        eapply reachable_steps;
          [eassumption|eapply steps_singleton; eassumption].
      + inv_steps.
        eapply rqrs_lbl_outs_disj; [| | |eassumption|eassumption]; eauto.
        eapply reachable_steps;
          [eassumption|eapply steps_singleton; eassumption].
    - eapply reducible_trans; try eassumption.
      + apply reducible_cons_2.
        * change (RlblInt oidx2 ridx2 rins2 routs2 :: RlblInt oidx ridx rins routs :: hst)
            with ([RlblInt oidx2 ridx2 rins2 routs2; RlblInt oidx ridx rins routs] ++ hst)
            in H8.
          eapply steps_split in H8; [|reflexivity].
          destruct H8 as [sti [? ?]].
          apply internal_commutes; auto.
          { red; intuition. }
          { inv_steps.
            eapply rqrs_lbl_ins_disj; [| | |eassumption|eassumption]; eauto.
            eapply reachable_steps; [|eapply steps_singleton; eassumption].
            eapply reachable_steps; eassumption.
          }
          { eapply DisjList_app_3 in H7; dest; assumption. }
          { inv_steps.
            eapply rqrs_lbl_outs_disj; [| | |eassumption|eassumption]; eauto.
            eapply reachable_steps; [|eapply steps_singleton; eassumption].
            eapply reachable_steps; eassumption.
          }
      + apply reducible_cons.
        red; intros.
        eapply IHAtomic; eauto.
        eapply DisjList_app_3 in H7; dest; assumption.
  Qed.
  
  Lemma rqrs_lbl_reducible:
    forall inits1 ins1 hst1 outs1 eouts1 lbl2 oidx2 ridx2 rins2 routs2,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      lbl2 = RlblInt oidx2 ridx2 rins2 routs2 ->
      ~ In oidx2 (oindsOf hst1) ->
      DisjList eouts1 rins2 ->
      Reducible sys (lbl2 :: hst1) (hst1 ++ [lbl2]).
  Proof.
    intros; red; intros.
    inv_steps.
    eapply rqrs_atomic_outs_inits_disj
      with (outs1:= outs1) (hst2:= [RlblInt oidx2 ridx2 rins2 routs2]) in H2.
    - eapply rqrs_lbl_reducible'; try eassumption; try reflexivity.
      econstructor; eauto.
    - eassumption.
    - subst; econstructor.
    - subst; simpl.
      apply (DisjList_singleton_2 idx_dec); eassumption.
    - eassumption.
    - eapply reachable_steps; eassumption.
    - eassumption.
    - apply steps_singleton; eassumption.
  Qed.

  Lemma rqrs_reducible':
    forall inits1 ins1 hst1 outs1 eouts1 inits2 ins2 hst2 outs2 eouts2,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
      DisjList (oindsOf hst1) (oindsOf hst2) ->
      DisjList eouts1 ins2 ->
      Reducible sys (hst2 ++ hst1) (hst1 ++ hst2).
  Proof.
    induction 2; simpl; intros; subst.
    - eapply rqrs_lbl_reducible; eauto.
      specialize (H0 oidx); destruct H0; intuition.
    - apply DisjList_comm, DisjList_cons in H6; dest.
      apply DisjList_comm in H4.
      apply DisjList_comm, DisjList_app_3 in H7; dest.
      apply DisjList_comm in H5; apply DisjList_comm in H6.
      eapply reducible_trans.
      + apply reducible_cons.
        apply IHAtomic; auto.
      + change (RlblInt oidx ridx rins routs :: hst1 ++ hst)
          with ((RlblInt oidx ridx rins routs :: hst1) ++ hst).
        replace (hst1 ++ RlblInt oidx ridx rins routs :: hst)
          with ((hst1 ++ [RlblInt oidx ridx rins routs]) ++ hst)
          by (rewrite <-app_assoc; reflexivity).
        apply reducible_app_2.
        eapply rqrs_lbl_reducible; eauto.
  Qed.

  Theorem rqrs_reducible:
    forall inits1 ins1 hst1 outs1 eouts1 inits2 ins2 hst2 outs2 eouts2,
      Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
      Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
      DisjList (oindsOf hst1) (oindsOf hst2) ->
      DisjList eouts1 inits2 ->
      Reducible sys (hst2 ++ hst1) (hst1 ++ hst2).
  Proof.
    intros; red; intros.
    eapply steps_split in H3; [|reflexivity].
    destruct H3 as [sti [? ?]].
    eapply rqrs_atomic_eouts_ins_disj in H2.
    - eapply rqrs_reducible'; eauto.
      eapply steps_append; eauto.
    - eassumption.
    - eassumption.
    - assumption.
    - eassumption.
    - eapply reachable_steps; eassumption.
    - eassumption.
    - eassumption.
  Qed.

End RqRsRed.

Close Scope list.
Close Scope fmap.

