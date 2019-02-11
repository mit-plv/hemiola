Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.
Require Import RqRsInvMsg RqRsInvLock RqRsInvAtomic.
Require Import RqUpRed RsUpRed RqRsRed.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

(** Proof sketch for the reducibility of downward-request labels:
 * 1) [phst] ⊆ tr(nlbl)^{-1}
 * 2) Let [olast(hst)] be the last object index of an [Atomic] history [hst].
 * 2-1) [olast(hst) ∈ tr(nlbl) -> oinds(hst) ⊆ tr(nlbl)]
 * 2-2) [olast(hst) ∈ tr(nlbl)^{-1} -> 
 *       exists preh posth, 
 *         hst = posth ++ preh /\
 *         ("preh" just consists of RqUp labels) /\
 *         oinds(posth) ⊆ tr(nlbl)^{-1}]
 * 3) Now define [LPush] and [RPush] as follows:
 *    [LPush hst ≜ olast(hst) ∈ tr(nlbl)]
 *    [RPush hst ≜ olast(hst) ∈ tr(nlbl)^{-1}]
 * 4) To check each condition in [PushableHst]:
 * 4-1) Left-or-right: [olast(hst)] is a single object index, 
 *      thus [in_dec eq_nat_dec olast(hst) tr(nlbl)] provides enough
 *      information.
 * 4-2) Left-push-reducibility: if [hst] is left-pushable, then by 2-1) and 3)
 *      we get [oinds(hst) ⊆ tr(nlbl)]. Now by 1) and a) we exactly get the
 *      reducibility.
 * 4-3) Right-push-reducibility: if [hst] is right-pushable, then by 2-2) 
 *      and 3) we have [preh] and [posth] that satisfy the conditions in 2-2).
 * 4-3-1) [preh] and [nlbl] are commutative since [preh] only consists of 
 *        RqUp labels.
 * 4-3-2) [posth] and [nlbl] are commutative by applying a).
 * 4-4) [LRPushable]: if [RPush hst1 /\ LPush hst2], then by 2-1), 2-2), 
 *      and 3) for [hst1] we have [preh1] and [posth1] that satisfy the
 *      conditions in 2-2). Now reasoning very similarly to 4-2) and 4-3):
 * 4-4-1) [preh1] and [hst2] are commutative since [preh1] only consists of
 *        RqUp labels.
 * 4-4-2) [posth1] and [hst2] are commutative by applying a).
 *
 *)

Section RqDownReduction.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).

  Section OnRqDown.
    Variables (oidxTo: IdxT)
              (rqDowns: list (Id Msg)).
    Hypothesis (Hrqd: RqDownMsgs dtr sys oidxTo rqDowns).

    Lemma rqDown_oinds:
      forall hst inits ins outs eouts,
        SubList rqDowns eouts ->
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          steps step_m sys st1 hst st2 ->
          DisjList (oindsOf hst) (subtreeIndsOf dtr oidxTo).
    Proof.
    Admitted.

    Lemma rqDown_olast_inside_tree:
      forall inits ins hst outs eouts,
        DisjList rqDowns inits ->
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2 loidx,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(bst_msgs)) rqDowns ->
          steps step_m sys st1 hst st2 ->
          lastOIdxOf hst = Some loidx ->
          In loidx (subtreeIndsOf dtr oidxTo) ->
          SubList (oindsOf hst) (subtreeIndsOf dtr oidxTo).
    Proof.
    Admitted.

    Lemma rqDown_olast_outside_tree:
      forall inits ins hst outs eouts,
        DisjList rqDowns inits ->
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2 loidx,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(bst_msgs)) rqDowns ->
          steps step_m sys st1 hst st2 ->
          lastOIdxOf hst = Some loidx ->
          ~ In loidx (subtreeIndsOf dtr oidxTo) ->
          exists phst ninits nins nhst nouts,
            hst = nhst ++ phst /\
            (phst = nil \/
             (exists pins pouts ruIdx rqUps,
                 Atomic msg_dec inits pins phst pouts rqUps /\
                 RqUpMsgs dtr ruIdx rqUps /\
                 RqUpHistory dtr phst rqUps /\
                 Forall (fun rqUp => rqEdgeUpFrom dtr oidxTo =
                                     Some (idOf rqUp)) rqUps)) /\
            SubList (oindsOf phst) (subtreeIndsOf dtr oidxTo) /\
            SubList ninits ins /\
            Atomic msg_dec ninits nins nhst nouts eouts /\
            DisjList (oindsOf nhst) (subtreeIndsOf dtr oidxTo).
    Proof.
    Admitted.

    Definition RqDownP (st: MState oifc) :=
      Forall (InMPI st.(bst_msgs)) rqDowns.

    Ltac disc_rule_custom ::=
      try disc_footprints_ok.

    Lemma rqDown_step_disj:
      forall st1 oidx ridx rins routs st2,
        Reachable (steps step_m) sys st1 ->
        RqDownP st1 ->
        DisjList rqDowns rins ->
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        DisjList rqDowns routs.
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      assert (Reachable (steps step_m) sys st2).
      { eapply reachable_steps; [eassumption|].
        eapply steps_singleton; eassumption.
      }
      pose proof (downLockInv_ok H0 H H6); clear H6.
      inv_step.
      good_locking_get obj.
      disc_rule_conds.
      red in H3; destruct Hrqd as [robj [rqDown ?]]; dest; subst.
      inv H3; clear H22; simpl in H20.
      
      red; intros [rrqDown rqm].
      destruct (in_dec (id_dec msg_dec) (rrqDown, rqm) [rqDown]); auto.
      destruct (in_dec (id_dec msg_dec) (rrqDown, rqm) routs); auto.
      exfalso.
      Common.dest_in; simpl in *.

      good_rqrs_rule_get rule.
      good_rqrs_rule_cases rule.

      - disc_rule_conds.
        destruct i0; auto; inv H3.
        rewrite H8 in H13; discriminate.
      - disc_rule_conds.
        destruct i0; auto; inv H3.
        rewrite H8 in H13; discriminate.

      - disc_rule_conds.
        + destruct i0; auto; inv H16.
          elim (rqrsDTree_rqUp_down_not_eq H _ _ H13 H9); reflexivity.
        + eapply RqRsDownMatch_rq_rs in H27;
            [|apply in_map with (f:= idOf) in i0; simpl in i0; eassumption].
          destruct H27 as [cidx [rsUp ?]]; dest.
          repeat disc_rule_minds; subst.
          eapply downLockInvORq_down_rqsQ_length_two_False; try eassumption.

          destruct H21; solve_q.
          erewrite findQ_In_NoDup_enqMsgs by eassumption.
          solve_q.
          rewrite filter_app; simpl.
          rewrite H8; simpl.
          rewrite app_length; simpl.
          eapply rqsQ_length_ge_one in H20; [|assumption].
          unfold rqsQ in H20; simpl in H20.
          omega.
        + eapply RqRsDownMatch_rq_rs in H13;
            [|apply in_map with (f:= idOf) in i0; simpl in i0; eassumption].
          destruct H13 as [cidx [rsUp ?]]; dest.
          repeat disc_rule_minds; subst.
          eapply downLockInvORq_down_rqsQ_length_two_False; try eassumption.

          destruct H21; solve_q.
          erewrite findQ_In_NoDup_enqMsgs by eassumption.
          apply parentIdxOf_not_eq in H16; [|destruct H; assumption].
          solve_q.
          rewrite filter_app; simpl.
          rewrite H8; simpl.
          rewrite app_length; simpl.
          eapply rqsQ_length_ge_one in H20; [|assumption].
          unfold rqsQ in H20; simpl in H20.
          omega.

      - disc_rule_conds.
        + destruct i0; auto; inv H3.
          rewrite H8 in H13; discriminate.
        + destruct i0; auto; inv H3.
          rewrite H8 in H13; discriminate.

      - disc_rule_conds.
        eapply RqRsDownMatch_rq_rs in H27;
          [|apply in_map with (f:= idOf) in i0; simpl in i0; eassumption].
        destruct H27 as [cidx [rsUp ?]]; dest.
        repeat disc_rule_minds; subst.
        eapply downLockInvORq_down_rqsQ_length_two_False; try eassumption.

        destruct H21; solve_q.
        erewrite findQ_In_NoDup_enqMsgs by eassumption.
        apply parentIdxOf_not_eq in H27; [|destruct H; assumption].
        solve_q.
        rewrite filter_app; simpl.
        rewrite H8; simpl.
        rewrite app_length; simpl.
        eapply rqsQ_length_ge_one in H20; [|assumption].
        unfold rqsQ in H20; simpl in H20.
        omega.
    Qed.
    
    Lemma rqDown_atomic_messages_indep:
      forall inits ins hst outs eouts,
        Atomic msg_dec inits ins hst outs eouts ->
        DisjList rqDowns inits ->
        forall st1,
          Reachable (steps step_m) sys st1 ->
          RqDownP st1 ->
          forall st2,
            steps step_m sys st1 hst st2 ->
            DisjList rqDowns outs.
    Proof.
      induction 1; simpl; intros; subst.
      - inv_steps.
        eapply rqDown_step_disj; eauto.
      - inv_steps.
        specialize (IHAtomic H5 _ H6 H7 _ H9).
        apply DisjList_comm, DisjList_app_4;
          [apply DisjList_comm in IHAtomic; assumption|].
        apply DisjList_comm in H5.
        assert (DisjList rqDowns rins).
        { eapply DisjList_comm, DisjList_SubList;
            [|eapply DisjList_comm; eassumption].
          eapply SubList_trans; [eassumption|].
          eapply atomic_eouts_in; eassumption.
        }
        eapply (atomic_messages_ins_ins msg_dec) in H; try eassumption.
        apply DisjList_comm.
        eapply rqDown_step_disj.
        + eapply reachable_steps; eassumption.
        + assumption.
        + eassumption.
        + eassumption.
    Qed.

    Lemma rqDown_lpush_rpush_messages_disj:
      forall rinits rins rhst routs reouts
             linits lins lhst louts leouts,
        Atomic msg_dec rinits rins rhst routs reouts ->
        DisjList (oindsOf rhst) (subtreeIndsOf dtr oidxTo) ->
        Atomic msg_dec linits lins lhst louts leouts ->
        SubList (oindsOf lhst) (subtreeIndsOf dtr oidxTo) ->
        forall st1,
          Reachable (steps step_m) sys st1 ->
          RqDownP st1 ->
          forall st2,
            steps step_m sys st1 (lhst ++ rhst) st2 ->
            DisjList reouts linits.
    Proof.
    Admitted.

    Lemma rqDown_lpush_rpush_unit_reducible:
      forall rinits rins rhst routs reouts
             linits lins lhst louts leouts,
        Atomic msg_dec rinits rins rhst routs reouts ->
        DisjList (oindsOf rhst) (subtreeIndsOf dtr oidxTo) ->
        Atomic msg_dec linits lins lhst louts leouts ->
        SubList (oindsOf lhst) (subtreeIndsOf dtr oidxTo) ->
        DisjList reouts linits ->
        Reducible sys (lhst ++ rhst) (rhst ++ lhst).
    Proof.
      intros.
      eapply rqrs_reducible; try eassumption.
      eapply DisjList_comm, DisjList_SubList; [eassumption|].
      apply DisjList_comm; assumption.
    Qed.
    
    Lemma rqDown_lpush_unit_reducible:
      forall pinits pins phst pouts peouts
             inits ins hst outs eouts loidx,
        PInitializing sys RqDownP phst ->
        Atomic msg_dec pinits pins phst pouts peouts ->
        SubList rqDowns peouts ->
        Atomic msg_dec inits ins hst outs eouts ->
        lastOIdxOf hst = Some loidx ->
        In loidx (subtreeIndsOf dtr oidxTo) ->
        DisjList peouts inits ->
        Reducible sys (hst ++ phst) (phst ++ hst).
    Proof.
      intros; red; intros.
      eapply steps_split in H6; [|reflexivity].
      destruct H6 as [sti [? ?]].
      eapply rqDown_lpush_rpush_unit_reducible; try eassumption.
      - eapply rqDown_oinds; try eassumption.
      - eapply rqDown_olast_inside_tree.
        + eapply DisjList_SubList; [|eassumption].
          eassumption.
        + eassumption.
        + eapply reachable_steps; [eassumption|].
          eassumption.
        + eapply H; eassumption.
        + eassumption.
        + eassumption.
        + eassumption.
      - eapply steps_append; eauto.
    Qed.

    Lemma rqDown_rpush_unit_reducible:
      forall inits ins hst outs eouts loidx ridx routs,
        Atomic msg_dec inits ins hst outs eouts ->
        lastOIdxOf hst = Some loidx ->
        ~ In loidx (subtreeIndsOf dtr oidxTo) ->
        DisjList rqDowns inits ->
        ReducibleP sys RqDownP (RlblInt oidxTo ridx rqDowns routs :: hst)
                   (hst ++ [RlblInt oidxTo ridx rqDowns routs]).
    Proof.
      intros; red; intros.
      inv_steps.
      pose proof (rqDown_olast_outside_tree H2 H Hr Hp H7 H0 H1).
      destruct H3 as [prhst [ninits [nins [nhst [nouts ?]]]]]; dest; subst.
      eapply steps_split in H7; [|reflexivity].
      destruct H7 as [sti [? ?]].

      rewrite <-app_assoc.
      eapply reducible_app_1; try assumption.
      - instantiate (1:= RlblInt oidxTo ridx rqDowns routs :: prhst).
        red; intros.
        destruct H4; subst; simpl in *.
        + inv_steps.
          apply steps_singleton; assumption.
        + destruct H4 as [prins [prouts [ruIdx [rqUps ?]]]]; dest.
          eapply rqUpHistory_lpush_lbl; try eassumption.
          destruct Hrrs as [? [? ?]].
          clear -Hrqd H12 H15.
          destruct Hrqd as [[rqDown rqdm] ?]; dest; subst.
          destruct H12 as [cidx [[rqUp rqum] ?]]; dest; subst.
          apply idsOf_DisjList; simpl in *.
          solve_midx_disj.
      - change (nhst ++ RlblInt oidxTo ridx rqDowns routs :: prhst)
          with (nhst ++ [RlblInt oidxTo ridx rqDowns routs] ++ prhst).
        rewrite app_assoc.
        eapply reducible_app_2; try assumption.
        + instantiate (1:= RlblInt oidxTo ridx rqDowns routs :: nhst).
          change (RlblInt oidxTo ridx rqDowns routs :: nhst)
            with ([RlblInt oidxTo ridx rqDowns routs] ++ nhst).
          eapply rqDown_lpush_rpush_unit_reducible; try eassumption.
          * constructor.
          * simpl; red; intros; Common.dest_in.
            apply parentChnsOf_subtreeIndsOf_self_in.
            { apply Hrrs. }
            { destruct Hrqd as [rqDown ?]; dest.
              unfold edgeDownTo, downEdgesTo in H13.
              destruct (parentChnsOf dtr e); simpl in H13; discriminate.
            }
          * eapply DisjList_SubList.
            { eapply atomic_eouts_in, H. }
            { apply DisjList_comm.
              eapply rqDown_atomic_messages_indep; try eassumption.
              eapply steps_append; eassumption.
            }
        + simpl; econstructor; [|eassumption].
          eapply steps_append; eassumption.
    Qed.

    Lemma rqDown_LRPushable_unit_reducible:
      forall rinits rins rhst routs reouts rloidx
             linits lins lhst louts leouts lloidx,
        Atomic msg_dec rinits rins rhst routs reouts ->
        DisjList rqDowns rinits ->
        lastOIdxOf rhst = Some rloidx ->
        ~ In rloidx (subtreeIndsOf dtr oidxTo) ->
        Atomic msg_dec linits lins lhst louts leouts ->
        DisjList rqDowns linits ->
        lastOIdxOf lhst = Some lloidx ->
        In lloidx (subtreeIndsOf dtr oidxTo) ->
        ReducibleP sys RqDownP (lhst ++ rhst) (rhst ++ lhst).
    Proof.
      intros; red; intros.
      eapply steps_split in H7; [|reflexivity].
      destruct H7 as [sti [? ?]].

      eapply rqDown_olast_inside_tree in H6;
        [|exact H4
         |eassumption
         |eapply reachable_steps; eassumption
         |eapply (atomic_messages_ins_ins msg_dec);
          try eapply H; try eassumption;
          apply DisjList_comm; assumption
         |eassumption
         |eassumption].
      clear H5.

      eapply rqDown_olast_outside_tree in H2;
        try exact H0; try eassumption.
      clear H1.
      destruct H2 as [prhst [ninits [nins [nrhst [nouts ?]]]]].
      dest; subst.

      rewrite <-app_assoc.
      eapply reducible_app_1; try assumption.
      - instantiate (1:= lhst ++ prhst).
        destruct H2; dest; subst; simpl.
        + rewrite app_nil_r; apply reducible_refl.
        + eapply rqUpHistory_lpush_unit_reducible; eauto.
          destruct Hrrs as [? [? ?]].
          eapply atomic_inside_tree_inits_disj_rqUps; try eassumption.
      - rewrite app_assoc.
        eapply reducible_app_2; try assumption.
        + instantiate (1:= lhst ++ nrhst).
          eapply rqDown_lpush_rpush_unit_reducible; try eassumption.
          eapply steps_split in H7; [|reflexivity].
          destruct H7 as [rsti [? ?]].
          eapply rqDown_lpush_rpush_messages_disj.
          * eassumption.
          * eassumption.
          * eassumption.
          * eassumption.
          * eapply reachable_steps; eassumption.
          * destruct H2; subst; simpl in *;
              [inv_steps; assumption|].
            destruct H2 as [pins [pouts [ruIdx [rqUps ?]]]]; dest.
            eapply (atomic_messages_ins_ins msg_dec).
            { eapply H2. }
            { eassumption. }
            { eassumption. }
            { eapply DisjList_comm, H0. }
          * eapply steps_append; eassumption.
        + rewrite <-app_assoc.
          eapply steps_append; eassumption.
    Qed.
    
  End OnRqDown.

End RqDownReduction.

