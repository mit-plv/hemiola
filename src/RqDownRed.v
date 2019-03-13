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

Section RqDownReduction.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypothesis (Hrrs: RqRsSys dtr sys).

  Section OnRqDown.
    Variables (cidx: IdxT) (pobj: Object oifc)
              (rqDowns: list (Id Msg)).
    Hypotheses (Hrqd: RqDownMsgs dtr sys cidx rqDowns)
               (Hpobj: In pobj sys.(sys_objs))
               (Hcp: parentIdxOf dtr cidx = Some (obj_idx pobj)).

    Lemma rqDown_oinds:
      forall hst inits ins outs eouts,
        SubList rqDowns eouts ->
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          steps step_m sys st1 hst st2 ->
          DisjList (oindsOf hst) (subtreeIndsOf dtr cidx).
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
          In loidx (subtreeIndsOf dtr cidx) ->
          SubList (oindsOf hst) (subtreeIndsOf dtr cidx).
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
          ~ In loidx (subtreeIndsOf dtr cidx) ->
          exists ruhst nhst,
            hst = nhst ++ ruhst /\
            (ruhst = nil \/
             exists roidx rqUps ruins ruouts,
               RqUpMsgs dtr roidx rqUps /\
               ~ In roidx (subtreeIndsOf dtr cidx) /\
               Atomic msg_dec inits ruins ruhst ruouts rqUps /\
               SubList rqUps ins /\
               (nhst = nil \/
                exists nins nouts,
                  Atomic msg_dec rqUps nins nhst nouts eouts)) /\
            DisjList (oindsOf nhst) (subtreeIndsOf dtr cidx).
    Proof.
    Admitted.

    Definition RqDownP (st: MState oifc) :=
      Forall (InMPI st.(bst_msgs)) rqDowns.

    Lemma rqDown_lpush_rpush_messages_disj:
      forall rinits rins rhst routs reouts
             linits lins lhst louts leouts,
        DisjList rqDowns rinits ->
        Atomic msg_dec rinits rins rhst routs reouts ->
        DisjList (oindsOf rhst) (subtreeIndsOf dtr cidx) ->
        DisjList rqDowns linits ->
        Atomic msg_dec linits lins lhst louts leouts ->
        SubList (oindsOf lhst) (subtreeIndsOf dtr cidx) ->
        forall st1,
          Reachable (steps step_m) sys st1 ->
          RqDownP st1 ->
          forall st2,
            steps step_m sys st1 (lhst ++ rhst) st2 ->
            DisjList reouts linits.
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      apply (DisjList_false_spec (id_dec msg_dec)).
      intros [midx msg] ? ?.
      unfold RqDownP in H9.
      destruct Hrqd as [cobj [[rqDown rqdm] ?]]; dest; subst.
      inv H9; clear H19.
      simpl in *.

      replace midx with rqDown in *.
      - eapply steps_split in H10; [|reflexivity].
        destruct H10 as [sti [? ?]].
        eapply atomic_rqDown_no_out
          with (cobj0:= cobj) (pobj0:= pobj) (rqDown0:= (rqDown, rqdm))
               (dmsg:= (rqDown, msg)) (st3:= st1) (outs:= routs); eauto.
        + eapply DisjList_In_2; [eassumption|].
          left; reflexivity.
        + eapply atomic_eouts_in; eauto.
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

    Lemma rqDown_lpush_rpush_unit_reducible:
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
    
    Lemma rqDown_lpush_unit_reducible:
      forall pinits pins phst pouts peouts
             inits ins hst outs eouts loidx,
        PInitializing sys RqDownP phst ->
        Atomic msg_dec pinits pins phst pouts peouts ->
        SubList rqDowns peouts ->
        Atomic msg_dec inits ins hst outs eouts ->
        lastOIdxOf hst = Some loidx ->
        In loidx (subtreeIndsOf dtr cidx) ->
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
        ~ In loidx (subtreeIndsOf dtr cidx) ->
        DisjList rqDowns inits ->
        ReducibleP sys RqDownP (RlblInt cidx ridx rqDowns routs :: hst)
                   (hst ++ [RlblInt cidx ridx rqDowns routs]).
    Proof.
      intros; red; intros.
      inv_steps.
      pose proof (rqDown_olast_outside_tree H2 H Hr Hp H7 H0 H1).
      destruct H3 as [ruhst [nhst ?]]; dest; subst.
      eapply steps_split in H7; [|reflexivity].
      destruct H7 as [sti [? ?]].

      destruct H4; subst.
      - rewrite app_nil_r in *; inv H3.
        eapply rqDown_lpush_rpush_unit_reducible; try eassumption.
        + constructor.
        + simpl; apply SubList_cons; [|apply SubList_nil].
          destruct Hrqd as [dobj [rqDown rqdm]]; dest; subst.
          apply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|].
          congruence.
        + red in Hp.
          destruct Hrqd as [dobj [[rqDown rqdm] ?]]; dest; subst.
          inv Hp; clear H12.
          eapply DisjList_SubList; [eapply atomic_eouts_in; eassumption|].
          apply (DisjList_singleton_2 (id_dec msg_dec)).
          eapply atomic_rqDown_inits_outs_disj; eauto.
          eapply DisjList_In_2; eauto.
          left; reflexivity.
        + simpl; econstructor; eauto.

      - destruct H4 as [roidx [rqUps [ruins [ruouts ?]]]]; dest.
        rewrite <-app_assoc.
        eapply reducible_app_1; try assumption.
        + instantiate (1:= RlblInt cidx ridx rqDowns routs :: ruhst).
          red; intros.
          eapply rqUpHistory_lpush_lbl with (rqUps0:= rqUps); try eassumption.
          * inv_steps.
            eapply rqUp_atomic; eauto.
            apply SubList_refl.
          * destruct Hrrs as [? [? ?]].
            clear -Hrqd H4 H13.
            destruct Hrqd as [dobj [[rqDown rqdm] ?]]; dest; subst.
            destruct H4 as [cidx [[rqUp rqum] ?]]; dest; subst.
            apply idsOf_DisjList; simpl in *.
            solve_midx_disj.
        + destruct H11; subst;
            [simpl in *; inv H6; econstructor; eauto|].
          destruct H11 as [nins [nouts ?]].
          change (nhst ++ RlblInt cidx ridx rqDowns routs :: ruhst)
            with (nhst ++ [RlblInt cidx ridx rqDowns routs] ++ ruhst).
          rewrite app_assoc.
          eapply reducible_app_2; try assumption.
          * instantiate (1:= RlblInt cidx ridx rqDowns routs :: nhst).
            change (RlblInt cidx ridx rqDowns routs :: nhst)
              with ([RlblInt cidx ridx rqDowns routs] ++ nhst).
            eapply rqDown_lpush_rpush_unit_reducible; try eassumption.
            { constructor. }
            { simpl; red; intros; Common.dest_in.
              apply edgeDownTo_subtreeIndsOf_self_in.
              { apply Hrrs. }
              { destruct Hrqd; dest; congruence. }
            }
            { eapply DisjList_SubList.
              { eapply atomic_eouts_in, H. }
              { apply DisjList_comm.
                red in Hp.
                destruct Hrqd as [dobj [[rqDown rqdm] ?]]; dest; subst.
                inv Hp; clear H18.
                apply (DisjList_singleton_1 (id_dec msg_dec)).
                eapply atomic_rqDown_inits_outs_disj; eauto.
                { destruct (H2 (rqDown, rqdm)); [|assumption].
                  elim H12; left; reflexivity.
                }
                { eapply steps_append; eassumption. }
              }
            }
          * simpl; econstructor; [|eassumption].
            eapply steps_append; eassumption.
    Qed.

    Lemma rqDown_LRPushable_unit_reducible:
      forall rinits rins rhst routs reouts rloidx
             linits lins lhst louts leouts lloidx,
        Atomic msg_dec rinits rins rhst routs reouts ->
        DisjList rqDowns rinits ->
        lastOIdxOf rhst = Some rloidx ->
        ~ In rloidx (subtreeIndsOf dtr cidx) ->
        Atomic msg_dec linits lins lhst louts leouts ->
        DisjList rqDowns linits ->
        lastOIdxOf lhst = Some lloidx ->
        In lloidx (subtreeIndsOf dtr cidx) ->
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
      destruct H2 as [ruhst [nhst ?]]; dest; subst.

      destruct H2; subst.
      - rewrite app_nil_r in *.
        eapply rqDown_lpush_rpush_unit_reducible; try eassumption.
        + eapply rqDown_lpush_rpush_messages_disj
            with (rinits:= rinits) (linits:= linits); eauto.
          eapply steps_append; eassumption.
        + eapply steps_append; eassumption.

      - destruct H1 as [roidx [rqUps [ruins [ruouts ?]]]]; dest.
        destruct H11; subst.
        * simpl in *.
          eapply rqUpHistory_lpush_unit_reducible; eauto.
          { eapply rqUp_atomic; eauto.
            apply SubList_refl.
          }
          { assert (Reachable (steps step_m) sys sti)
              by (eapply reachable_steps; eassumption).
            clear Hr.
            destruct H1 as [rcidx [rqUp ?]]; dest; subst.
            eapply atomic_inside_tree_inits_disj_rqUps
              with (rqFrom:= rcidx); eauto.
            eapply outside_child_in; try apply Hrrs; eassumption.
          }
          { eapply steps_append; eauto. }
        * destruct H11 as [nins [nouts ?]].
          rewrite <-app_assoc.
          eapply reducible_app_1; try assumption.
          { instantiate (1:= lhst ++ ruhst).
            eapply rqUpHistory_lpush_unit_reducible; eauto.
            { eapply steps_split in H7; [|reflexivity].
              destruct H7 as [rsti [? ?]].
              eapply rqUp_atomic; eauto.
              apply SubList_refl.
            }
            { assert (Reachable (steps step_m) sys sti)
                by (eapply reachable_steps; eassumption).
              clear Hr.
              destruct H1 as [rcidx [rqUp ?]]; dest; subst.
              eapply atomic_inside_tree_inits_disj_rqUps
                with (rqFrom:= rcidx); eauto.
              eapply outside_child_in; try apply Hrrs; eassumption.
            }
          }
          { rewrite app_assoc.
            eapply reducible_app_2; try assumption.
            { instantiate (1:= lhst ++ nhst).
              eapply rqDown_lpush_rpush_unit_reducible; try eassumption.
              eapply steps_split in H7; [|reflexivity].
              destruct H7 as [rsti [? ?]].
              assert (DisjList rqDowns rqUps).
              { eapply DisjList_comm, DisjList_SubList; [eassumption|].
                apply DisjList_comm.
                unfold RqDownP in Hp.
                destruct Hrqd as [dobj [[rqDown rqdm] ?]]; dest; subst.
                inv Hp.
                apply (DisjList_singleton_1 (id_dec msg_dec)).
                eapply atomic_rqDown_inits_ins_disj; eauto;
                  [|eapply steps_append; eauto].
                specialize (H0 (rqDown, rqdm)); destruct H0; auto.
                elim H0; left; reflexivity.
              }
              eapply rqDown_lpush_rpush_messages_disj
                with (rinits:= rqUps) (linits:= linits) (st1:= rsti); eauto.
              { eapply (atomic_messages_ins_ins msg_dec).
                { eapply H9. }
                { eassumption. }
                { eassumption. }
                { eapply DisjList_comm, H0. }
              }
              { eapply steps_append; eassumption. }
            }
            { rewrite <-app_assoc.
              eapply steps_append; eassumption.
            }
          }
    Qed.
    
  End OnRqDown.

End RqDownReduction.

Close Scope list.
Close Scope fmap.

