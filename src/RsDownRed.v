Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts.
Require Import RqRsInvMsg RqRsInvLock RqRsInvAtomic RqRsInvSep.
Require Import RqUpRed RsUpRed RqRsRed.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section RsDownReduction.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).

  Section OnRsDown.
    Variables (cidx: IdxT) (pobj: Object oifc)
              (rsDowns: list (Id Msg)).
    Hypotheses (Hrsd: RsDownMsgs dtr sys cidx rsDowns)
               (Hpobj: In pobj sys.(sys_objs))
               (Hcp: parentIdxOf dtr cidx = Some (obj_idx pobj)).

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
                 Forall (fun rqUp => rqEdgeUpFrom dtr cidx =
                                     Some (idOf rqUp)) rqUps)) /\
            SubList (oindsOf phst) (subtreeIndsOf dtr cidx) /\
            SubList ninits ins /\
            Atomic msg_dec ninits nins nhst nouts eouts /\
            DisjList (oindsOf nhst) (subtreeIndsOf dtr cidx).
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
          In loidx (subtreeIndsOf dtr cidx) ->
          SubList (oindsOf hst) (subtreeIndsOf dtr cidx).
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      destruct Hrsd as [cobj [rsDown ?]]; dest; subst.
      pose proof (edgeDownTo_Some H _ H11).
      destruct H9 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      eapply atomic_rsDown_separation_inside
        with (cobj0:= cobj) (pobj0:= pobj); eauto.
      - apply DisjList_cons in H2; dest; assumption.
      - eapply lastOIdxOf_Some_oindsOf_In; eauto.
    Qed.

    Lemma rsDown_olast_outside_tree:
      forall inits ins hst outs eouts,
        DisjList rsDowns inits ->
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2 loidx,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(bst_msgs)) rsDowns ->
          steps step_m sys st1 hst st2 ->
          lastOIdxOf hst = Some loidx ->
          ~ In loidx (subtreeIndsOf dtr cidx) ->
          DisjList (oindsOf hst) (subtreeIndsOf dtr cidx).
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      destruct Hrsd as [cobj [rsDown ?]]; dest; subst.
      pose proof (edgeDownTo_Some H _ H11).
      destruct H9 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      eapply atomic_rsDown_separation_outside
             with (cobj0:= cobj) (pobj0:= pobj); eauto.
      - apply DisjList_cons in H2; dest; assumption.
      - eapply lastOIdxOf_Some_oindsOf_In; eauto.
    Qed.

    Definition RsDownP (st: MState oifc) :=
      Forall (InMPI st.(bst_msgs)) rsDowns.

    Ltac disc_rule_custom ::=
      try disc_footprints_ok.

    Lemma rsDown_lpush_rpush_messages_disj:
      forall rinits rins rhst routs reouts
             linits lins lhst louts leouts,
        DisjList rsDowns rinits ->
        Atomic msg_dec rinits rins rhst routs reouts ->
        DisjList (oindsOf rhst) (subtreeIndsOf dtr cidx) ->
        DisjList rsDowns linits ->
        Atomic msg_dec linits lins lhst louts leouts ->
        SubList (oindsOf lhst) (subtreeIndsOf dtr cidx) ->
        forall st1,
          Reachable (steps step_m) sys st1 ->
          RsDownP st1 ->
          forall st2,
            steps step_m sys st1 (lhst ++ rhst) st2 ->
            DisjList reouts linits.
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      apply (DisjList_false_spec (id_dec msg_dec)).
      intros [midx msg] ? ?.
      unfold RsDownP in H9.
      destruct Hrsd as [cobj [[rsDown rsdm] ?]]; dest; subst.
      inv H9; clear H19.
      simpl in *.

      replace midx with rsDown in *.
      - eapply steps_split in H10; [|reflexivity].
        destruct H10 as [sti [? ?]].
        eapply atomic_rsDown_no_in
          with (cobj0:= cobj) (pobj0:= pobj) (rsDown0:= (rsDown, rsdm))
               (dmsg:= (rsDown, msg)) (st3:= sti); eauto.
        + eapply (atomic_messages_in_in msg_dec); try apply H3; eauto.
          eapply DisjList_In_2; [eassumption|].
          left; reflexivity.
        + eapply DisjList_In_2; [eassumption|].
          left; reflexivity.
        + eapply atomic_inits_in; eauto.

      - eapply steps_split in H10; [|reflexivity].
        destruct H10 as [sti [? ?]].
        eapply atomic_ext_outs_in_history in H3; eauto.
        rewrite Forall_forall in H3; specialize (H3 _ H11).
        destruct H3 as [ofrom [? ?]].
        eapply atomic_inits_in_history with (s1:= sti) in H6; eauto.
        rewrite Forall_forall in H6; specialize (H6 _ H12).
        destruct H6 as [oto [? ?]].
        destruct H3 as [|[|]], H6 as [|[|]];
          try (dest; exfalso; solve_midx_false; fail).
        + exfalso; simpl in *.
          destruct H6 as [cidx [? ?]].
          disc_rule_conds.
          eapply DisjList_In_2 in H13; [|eassumption].
          apply H7 in H17.
          elim H13.
          eapply inside_child_in; try apply Hrrs; eauto.
        + exfalso; simpl in *.
          destruct H6 as [cidx [? ?]].
          disc_rule_conds.
          eapply DisjList_In_2 in H13; [|eassumption].
          apply H7 in H17.
          elim H13.
          eapply inside_child_in; try apply Hrrs; eauto.
        + simpl in *; destruct H3 as [cidx [? ?]].
          disc_rule_conds.
          eapply DisjList_In_2 in H13; [|eassumption].
          apply H7 in H17.
          eapply inside_child_outside_parent_case in H17;
            try apply Hrrs; eauto; subst.
          disc_rule_conds.
    Qed.
    
    Lemma rsDown_lpush_rpush_unit_reducible:
      forall rinits rins rhst routs reouts
             linits lins lhst louts leouts,
        Atomic msg_dec rinits rins rhst routs reouts ->
        DisjList (oindsOf rhst) (subtreeIndsOf dtr cidx) ->
        Atomic msg_dec linits lins lhst louts leouts ->
        SubList (oindsOf lhst) (subtreeIndsOf dtr cidx) ->
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
        In loidx (subtreeIndsOf dtr cidx) ->
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
        ~ In loidx (subtreeIndsOf dtr cidx) ->
        DisjList rsDowns inits ->
        ReducibleP sys RsDownP (RlblInt cidx ridx rsDowns routs :: hst)
                   (hst ++ [RlblInt cidx ridx rsDowns routs]).
    Proof.
      destruct Hrrs as [? [? ?]]; intros; red; intros.
      inv_steps.
      eapply rsDown_lpush_rpush_unit_reducible; try eassumption.
      - eapply rsDown_olast_outside_tree; eassumption.
      - constructor.
      - simpl; red; intros; Common.dest_in.
        apply edgeDownTo_subtreeIndsOf_self_in.
        + apply Hrrs.
        + destruct Hrsd as [rsDown ?]; dest; congruence.
      - eapply DisjList_SubList.
        + eapply atomic_eouts_in; eassumption.
        + apply DisjList_comm.
          red in Hp.
          destruct Hrsd as [dobj [[rsDown rsdm] ?]]; dest; subst.
          inv Hp; clear H14.
          apply (DisjList_singleton_1 (id_dec msg_dec)).
          simpl in H8.
          pose proof (edgeDownTo_Some H _ H8).
          destruct H6 as [rqUp [rsUp [pidx ?]]]; dest.
          eapply atomic_rsDown_inits_outs_disj; eauto.
          destruct (H5 (rsDown, rsdm)); [|auto].
          elim H15; left; reflexivity.
      - simpl; econstructor; eassumption.
    Qed.

    Lemma rsDown_LRPushable_unit_reducible:
      forall rinits rins rhst routs reouts rloidx
             linits lins lhst louts leouts lloidx,
        Atomic msg_dec rinits rins rhst routs reouts ->
        DisjList rsDowns rinits ->
        lastOIdxOf rhst = Some rloidx ->
        ~ In rloidx (subtreeIndsOf dtr cidx) ->
        Atomic msg_dec linits lins lhst louts leouts ->
        DisjList rsDowns linits ->
        lastOIdxOf lhst = Some lloidx ->
        In lloidx (subtreeIndsOf dtr cidx) ->
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
      - eapply rsDown_lpush_rpush_messages_disj
          with (linits := linits) (rinits := rinits); try eassumption.
        eapply steps_append; eassumption.
      - eapply steps_append; eassumption.
    Qed.
    
  End OnRsDown.

End RsDownReduction.

Close Scope list.
Close Scope fmap.

