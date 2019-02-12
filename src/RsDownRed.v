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

(** Proof sketch for the reducibility of downward-response labels:
 * 1) [exists preh posth, 
 *       phst = posth ++ preh /\
 *       ("preh" just consists of RqUp labels) /\
 *       oinds(posth) ⊆ tr(nlbl)^{-1}]
 * 2) Let [olast(hst)] be the last object index of an [Atomic] history [hst].
 * 2-1) [olast(hst) ∈ tr(nlbl) -> oinds(hst) ⊆ tr(nlbl)]
 * 2-2) [olast(hst) ∈ tr(nlbl)^{-1} -> oinds(hst) ⊆ tr(nlbl)^{-1}]
 *      This part differs from the one for downward-requests since both upward
 *      requests and upward responses cannot happen when a downward-response label is
 *      in the message pool.
 * 3) Define [LPush] and [RPush] as follows:
 *    [LPush hst ≜ olast(hst) ∈ tr(nlbl)]
 *    [RPush hst ≜ olast(hst) ∈ tr(nlbl)^{-1}]
 * 4) Conditions of [PushableHst] are easier to prove, mostly by a).
 *)

Section RsDownReduction.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).

  Section OnRsDown.
    Variables (oidxTo: IdxT)
              (rsDowns: list (Id Msg)).
    Hypothesis (Hrsd: RsDownMsgs dtr sys oidxTo rsDowns).

    Lemma rsDown_oinds:
      forall inits ins hst outs eouts,
        SubList rsDowns eouts ->
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          steps step_m sys st1 hst st2 ->
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

    Lemma rsDown_olast_inside_tree:
      forall inits ins hst outs eouts,
        DisjList rsDowns inits ->
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2 loidx,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(bst_msgs)) rsDowns ->
          steps step_m sys st1 hst st2 ->
          lastOIdxOf hst = Some loidx ->
          In loidx (subtreeIndsOf dtr oidxTo) ->
          SubList (oindsOf hst) (subtreeIndsOf dtr oidxTo).
    Proof.
    Admitted.

    Lemma rsDown_olast_outside_tree:
      forall inits ins hst outs eouts,
        DisjList rsDowns inits ->
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2 loidx,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(bst_msgs)) rsDowns ->
          steps step_m sys st1 hst st2 ->
          lastOIdxOf hst = Some loidx ->
          ~ In loidx (subtreeIndsOf dtr oidxTo) ->
          DisjList (oindsOf hst) (subtreeIndsOf dtr oidxTo).
    Proof.
    Admitted.

    Definition RsDownP (st: MState oifc) :=
      Forall (InMPI st.(bst_msgs)) rsDowns.

    Ltac disc_rule_custom ::=
      try disc_footprints_ok.

    Lemma rsDown_step_disj:
      forall st1 oidx ridx rins routs st2,
        Reachable (steps step_m) sys st1 ->
        RsDownP st1 ->
        DisjList rsDowns rins ->
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        DisjList rsDowns routs.
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      assert (Reachable (steps step_m) sys st2).
      { eapply reachable_steps; [eassumption|].
        eapply steps_singleton; eassumption.
      }
      pose proof (upLockInv_ok H0 H H6) as Hlinv; clear H6.
      pose proof (footprints_ok H0 H2) as Hfinv.
      inv_step.
      red in H3; destruct Hrsd as [robj [rsDown ?]]; dest; subst.
      inv H3; clear H19; simpl in H12.
      pose proof (edgeDownTo_Some H _ H7).
      destruct H3 as [rqUp [rsUp [pidx ?]]]; dest.
      good_locking_get robj.
      
      red; intros [rrsDown rsm].
      destruct (in_dec (id_dec msg_dec) (rrsDown, rsm) [rsDown]); auto.
      destruct (in_dec (id_dec msg_dec) (rrsDown, rsm) routs); auto.
      exfalso.
      Common.dest_in; simpl in *.

      good_rqrs_rule_get rule.
      good_rqrs_rule_cases rule.

      - disc_rule_conds.
        destruct i0; auto; inv H15.
        repeat disc_rule_minds.
        eapply upLockInvORq_down_rssQ_length_two_False; try eassumption.
        solve_q.
        rewrite filter_app; simpl.
        rewrite H24; simpl.
        rewrite app_length; simpl.
        eapply rssQ_length_ge_one in H12; [|assumption].
        unfold rssQ in H12; simpl in H12.
        omega.

      - disc_rule_conds.
        destruct i0; auto; inv H15.
        elim (rqrsDTree_rsUp_down_not_eq H _ _ H37 H7); reflexivity.

      - disc_rule_conds.
        + destruct i0; auto; inv H15.
          disc_rule_conds.
        + rewrite Forall_forall in H40; specialize (H40 _ i0).
          simpl in H40; rewrite H40 in H6; discriminate.
        + rewrite Forall_forall in H40; specialize (H40 _ i0).
          simpl in H40; rewrite H40 in H6; discriminate.

      - good_footprint_get (obj_idx obj).
        disc_rule_conds.
        + destruct i0; auto; inv H28.
          eapply upLockInvORq_down_rssQ_length_two_False; try eassumption.
          solve_q.
          apply parentIdxOf_not_eq in H15; [|destruct H; assumption].
          solve_q.
          rewrite filter_app; simpl.
          rewrite H27; simpl.
          rewrite app_length; simpl.
          eapply rssQ_length_ge_one in H12; [|assumption].
          unfold rssQ in H12; simpl in H12.
          omega.
        + destruct i0; auto; inv H24.
          eapply upLockInvORq_down_rssQ_length_two_False; try eassumption.
          rewrite <-H37 in H30.
          solve_q.
          rewrite filter_app; simpl.
          rewrite H26; simpl.
          rewrite app_length; simpl.
          eapply rssQ_length_ge_one in H12; [|assumption].
          unfold rssQ in H12; simpl in H12.
          omega.
        + destruct i0; auto; inv H27.
          elim (rqrsDTree_rsUp_down_not_eq H _ _ H24 H7); reflexivity.

      - disc_rule_conds.
        rewrite Forall_forall in H35; specialize (H35 _ i0).
        simpl in H35; rewrite H35 in H6; discriminate.
    Qed.

    Lemma rsDown_atomic_messages_indep:
      forall inits ins hst outs eouts,
        Atomic msg_dec inits ins hst outs eouts ->
        DisjList rsDowns inits ->
        forall st1,
          Reachable (steps step_m) sys st1 ->
          RsDownP st1 ->
          forall st2,
            steps step_m sys st1 hst st2 ->
            DisjList rsDowns outs.
    Proof.
      induction 1; simpl; intros; subst.
      - inv_steps.
        eapply rsDown_step_disj; eauto.
      - inv_steps.
        specialize (IHAtomic H5 _ H6 H7 _ H9).
        apply DisjList_comm, DisjList_app_4;
          [apply DisjList_comm in IHAtomic; assumption|].
        apply DisjList_comm in H5.
        assert (DisjList rsDowns rins).
        { eapply DisjList_comm, DisjList_SubList;
            [|eapply DisjList_comm; eassumption].
          eapply SubList_trans; [eassumption|].
          eapply atomic_eouts_in; eassumption.
        }
        eapply (atomic_messages_ins_ins msg_dec) in H; try eassumption.
        apply DisjList_comm.
        eapply rsDown_step_disj.
        + eapply reachable_steps; eassumption.
        + assumption.
        + eassumption.
        + eassumption.
    Qed.

    Lemma rsDown_lpush_rpush_messages_disj:
      forall rinits rins rhst routs reouts
             linits lins lhst louts leouts,
        Atomic msg_dec rinits rins rhst routs reouts ->
        DisjList (oindsOf rhst) (subtreeIndsOf dtr oidxTo) ->
        Atomic msg_dec linits lins lhst louts leouts ->
        SubList (oindsOf lhst) (subtreeIndsOf dtr oidxTo) ->
        forall st1,
          Reachable (steps step_m) sys st1 ->
          RsDownP st1 ->
          forall st2,
            steps step_m sys st1 (lhst ++ rhst) st2 ->
            DisjList reouts linits.
    Proof.
    Admitted.
    
    Lemma rsDown_lpush_rpush_unit_reducible:
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
    
    Lemma rsDown_lpush_unit_reducible:
      forall pinits pins phst pouts peouts
             inits ins hst outs eouts loidx,
        PInitializing sys RsDownP phst ->
        Atomic msg_dec pinits pins phst pouts peouts ->
        SubList rsDowns peouts ->
        Atomic msg_dec inits ins hst outs eouts ->
        lastOIdxOf hst = Some loidx ->
        In loidx (subtreeIndsOf dtr oidxTo) ->
        DisjList peouts inits ->
        Reducible sys (hst ++ phst) (phst ++ hst).
    Proof.
      intros; red; intros.
      eapply steps_split in H6; [|reflexivity].
      destruct H6 as [sti [? ?]].

      pose proof (rsDown_oinds H1 H0 Hr H6).
      destruct H8 as [prhst [ninits [nins [nphst [nouts ?]]]]].
      dest; subst.
      eapply steps_split in H6; [|reflexivity].
      destruct H6 as [psti [? ?]].
      eapply rsDown_olast_inside_tree in H4;
        [|eapply DisjList_SubList; eassumption
         |eassumption
         |eapply reachable_steps; [eassumption|];
          eapply steps_append; eassumption
         |eapply H; eapply steps_append; eassumption
         |eassumption
         |eassumption].

      rewrite <-app_assoc.
      eapply reducible_app_1; try assumption.
      - instantiate (1:= hst ++ prhst).
        destruct H9; subst; simpl in *.
        + rewrite app_nil_r; apply reducible_refl.
        + destruct H9 as [prins [prouts [ruIdx [rqUps ?]]]]; dest.
          eapply rqUpHistory_lpush_unit_reducible; eauto.
          assert (Reachable (steps step_m) sys sti)
            by (do 2 (eapply reachable_steps; [|eassumption]);
                assumption).
          clear Hr.
          eapply atomic_inside_tree_inits_disj_rqUps; eauto.
      - rewrite app_assoc.
        eapply reducible_app_2; try assumption.
        + instantiate (1:= hst ++ nphst).
          eapply rsDown_lpush_rpush_unit_reducible; try eassumption.
        + rewrite <-app_assoc.
          eapply steps_append; [|eassumption].
          eapply steps_append; eassumption.
    Qed.

    Lemma rsDown_rpush_unit_reducible:
      forall inits ins hst outs eouts loidx ridx routs,
        Atomic msg_dec inits ins hst outs eouts ->
        lastOIdxOf hst = Some loidx ->
        ~ In loidx (subtreeIndsOf dtr oidxTo) ->
        DisjList rsDowns inits ->
        ReducibleP sys RsDownP (RlblInt oidxTo ridx rsDowns routs :: hst)
                   (hst ++ [RlblInt oidxTo ridx rsDowns routs]).
    Proof.
      intros; red; intros.
      inv_steps.
      eapply rsDown_lpush_rpush_unit_reducible; try eassumption.
      - eapply rsDown_olast_outside_tree; eassumption.
      - constructor.
      - simpl; red; intros; Common.dest_in.
        apply parentChnsOf_subtreeIndsOf_self_in.
        + apply Hrrs.
        + destruct Hrsd as [rsDown ?]; dest.
          unfold edgeDownTo, downEdgesTo in H5.
          destruct (parentChnsOf dtr e); simpl in H5; discriminate.
      - eapply DisjList_SubList.
        + eapply atomic_eouts_in; eassumption.
        + apply DisjList_comm.
          eapply rsDown_atomic_messages_indep; eassumption.
      - simpl; econstructor; eassumption.
    Qed.

    Lemma rsDown_LRPushable_unit_reducible:
      forall rinits rins rhst routs reouts rloidx
             linits lins lhst louts leouts lloidx,
        Atomic msg_dec rinits rins rhst routs reouts ->
        DisjList rsDowns rinits ->
        lastOIdxOf rhst = Some rloidx ->
        ~ In rloidx (subtreeIndsOf dtr oidxTo) ->
        Atomic msg_dec linits lins lhst louts leouts ->
        DisjList rsDowns linits ->
        lastOIdxOf lhst = Some lloidx ->
        In lloidx (subtreeIndsOf dtr oidxTo) ->
        ReducibleP sys RsDownP (lhst ++ rhst) (rhst ++ lhst).
    Proof.
      intros; red; intros.
      eapply steps_split in H7; [|reflexivity].
      destruct H7 as [sti [? ?]].
      eapply rsDown_olast_inside_tree in H6;
        [|exact H4
         |eassumption
         |eapply reachable_steps; eassumption
         |eapply (atomic_messages_ins_ins msg_dec);
          try eapply H; try eassumption;
          apply DisjList_comm; assumption
         |eassumption
         |eassumption].
      clear H5.
      eapply rsDown_olast_outside_tree in H2;
        try exact H0; try eassumption.
      clear H1.
      eapply rsDown_lpush_rpush_unit_reducible; try eassumption.
      - eapply rsDown_lpush_rpush_messages_disj; try eassumption.
        eapply steps_append; eassumption.
      - eapply steps_append; eassumption.
    Qed.
    
  End OnRsDown.

End RsDownReduction.

