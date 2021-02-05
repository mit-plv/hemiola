Require Import PeanoNat Lia List.
Require Import Common FMap IndexSupport.
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
  Context `{dv: DecValue} `{oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System).

  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (oinvs: IdxT -> ObjInv)
             (Hrrs: RqRsSys dtr sys oinvs).

  Section OnRqDown.
    Variables (cidx: IdxT) (pobj: Object)
              (rqDowns: list (Id Msg)).
    Hypotheses (Hrqd: RqDownMsgs dtr sys cidx rqDowns)
               (Hpobj: In pobj sys.(sys_objs))
               (Hcp: parentIdxOf dtr cidx = Some (obj_idx pobj)).

    Lemma rqDown_oinds:
      forall hst inits ins outs eouts,
        SubList rqDowns eouts ->
        Atomic inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          steps step_m sys st1 hst st2 ->
          DisjList (oindsOf hst) (subtreeIndsOf dtr cidx).
    Proof.
      intros.
      destruct Hrqd as [cobj [[rqDown rqdm] ?]]; dest; subst; simpl in *.
      eapply atomic_rqDown_covers with (rqDown0:= (rqDown, rqdm)); eauto.
      - red; auto.
      - apply SubList_singleton_In; auto.
    Qed.

    Lemma rqDown_olast_inside_tree:
      forall inits ins hst outs eouts,
        DisjList rqDowns inits ->
        Atomic inits ins hst outs eouts ->
        forall st1 st2 loidx,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(st_msgs)) rqDowns ->
          steps step_m sys st1 hst st2 ->
          lastOIdxOf hst = Some loidx ->
          In loidx (subtreeIndsOf dtr cidx) ->
          SubList (oindsOf hst) (subtreeIndsOf dtr cidx).
    Proof.
      intros.
      destruct Hrqd as [cobj [[rqDown rqdm] ?]]; dest; subst; simpl in *.
      inv H2; clear H12.
      pose proof H0.
      eapply rqUp_start_ok in H2; eauto.
      destruct H2 as [ruhst [nhst ?]]; dest; subst.
      assert (~ In (rqDown, rqdm) inits).
      { eapply DisjList_In_2; [eassumption|].
        left; reflexivity.
      }
      clear H.

      destruct H6; subst.
      - rewrite app_nil_r in *.
        eapply atomic_NonRqUp_rqDown_separation_inside
          with (cobj0:= cobj) (pobj0:= pobj) (rqDown0:= (rqDown, rqdm)); eauto.
        eapply lastOIdxOf_Some_oindsOf_In; eauto.

      - destruct H as [roidx [rqUps [ruins [ruouts ?]]]]; dest.
        pose proof H.
        destruct H14 as [cidx [rqUp [? _]]]; subst.
        destruct H13; subst.
        + simpl in *; clear H10.
          eapply rqUp_atomic_lastOIdxOf in H4; eauto; [|right; eauto].
          dest; eapply rqUp_atomic_bounded; eauto.
          right; auto.
        + destruct H13 as [nins [nouts ?]]; dest.
          rewrite oindsOf_app.
          eapply steps_split in H3; [|reflexivity].
          destruct H3 as [sti [? ?]].

          assert (SubList (oindsOf nhst) (subtreeIndsOf dtr (obj_idx cobj))).
          { eapply atomic_NonRqUp_rqDown_separation_inside
              with (cobj0:= cobj) (pobj0:= pobj)
                   (rqDown0:= (rqDown, rqdm)) (s1:= sti) (ioidx:= loidx); eauto.
            { eapply atomic_messages_in_in; try eapply H6; eauto. }
            { intro Hx; apply H12 in Hx.
              eapply atomic_rqDown_inits_outs_disj
                with (cidx0:= obj_idx cobj) (rqDown0:= (rqDown, rqdm))
                     (hst:= nhst ++ ruhst); eauto.
              eapply steps_append; eauto.
            }
            { eapply lastOIdxOf_Some_oindsOf_In; eauto.
              rewrite lastOIdxOf_app in H4; [|intro Hx; subst; inv H13].
              assumption.
            }
          }
          apply SubList_app_3; [assumption|].
          apply H16 in H14.
          apply subtreeIndsOf_SubList in H14; [|apply Hrrs].
          eapply SubList_trans; [|eapply H14].
          eapply rqUp_atomic_inside_tree; eauto.
          * discriminate.
          * right; auto.
    Qed.

    Lemma rqDown_olast_outside_tree:
      forall inits ins hst outs eouts,
        DisjList rqDowns inits ->
        Atomic inits ins hst outs eouts ->
        forall st1 st2 loidx,
          Reachable (steps step_m) sys st1 ->
          Forall (InMPI st1.(st_msgs)) rqDowns ->
          steps step_m sys st1 hst st2 ->
          lastOIdxOf hst = Some loidx ->
          ~ In loidx (subtreeIndsOf dtr cidx) ->
          exists ruhst nhst,
            hst = nhst ++ ruhst /\
            (ruhst = nil \/
             exists roidx rqUps ruins ruouts,
               RqUpMsgsP dtr roidx rqUps /\
               ~ In roidx (subtreeIndsOf dtr cidx) /\
               Atomic inits ruins ruhst ruouts rqUps /\
               SubList rqUps outs /\
               (nhst = nil \/
                exists nins nouts,
                  Atomic rqUps nins nhst nouts eouts)) /\
            DisjList (oindsOf nhst) (subtreeIndsOf dtr cidx).
    Proof.
      intros.
      destruct Hrqd as [cobj [[rqDown rqdm] ?]]; dest; subst; simpl in *.
      inv H2; clear H12.
      pose proof H0.
      eapply rqUp_start_ok in H2; eauto.
      destruct H2 as [ruhst [nhst ?]]; dest; subst.
      exists ruhst, nhst.
      assert (~ In (rqDown, rqdm) inits).
      { eapply DisjList_In_2; [eassumption|].
        left; reflexivity.
      }
      clear H.

      destruct H6; subst.
      - rewrite app_nil_r in *.
        repeat ssplit; [reflexivity|left; reflexivity|].
        eapply atomic_NonRqUp_rqDown_separation_outside
          with (cobj0:= cobj) (pobj0:= pobj) (rqDown0:= (rqDown, rqdm))
               (ioidx:= loidx); eauto.
        eapply lastOIdxOf_Some_oindsOf_In; eauto.

      - destruct H as [roidx [rqUps [ruins [ruouts ?]]]]; dest.
        pose proof H.
        destruct H14 as [cidx [rqUp [? _]]]; subst rqUps.
        destruct H13; subst.
        + simpl in *; clear H10.
          repeat ssplit; [reflexivity| |apply DisjList_nil_1].
          right; exists roidx, [rqUp], ruins, ruouts.
          repeat ssplit; try assumption.
          * eapply rqUp_atomic_lastOIdxOf in H6; eauto; [|right; eauto].
            dest; eapply outside_parent_out; try apply Hrrs; eauto.
          * left; reflexivity.

        + destruct H13 as [nins [nouts ?]]; dest.
          assert (DisjList (oindsOf nhst) (subtreeIndsOf dtr (obj_idx cobj))).
          { eapply steps_split in H3; [|reflexivity].
            destruct H3 as [sti [? ?]].
            eapply atomic_NonRqUp_rqDown_separation_outside
              with (cobj0:= cobj) (pobj0:= pobj) (rqDown0:= (rqDown, rqdm))
                   (ioidx:= loidx) (s1:= sti); eauto.
            { eapply atomic_messages_in_in; try eapply H6; eauto. }
            { intro Hx; apply H12 in Hx.
              eapply atomic_rqDown_inits_outs_disj
                with (cidx0:= obj_idx cobj) (rqDown0:= (rqDown, rqdm))
                     (hst:= nhst ++ ruhst); eauto.
              eapply steps_append; eauto.
            }
            { eapply lastOIdxOf_Some_oindsOf_In; eauto.
              rewrite lastOIdxOf_app in H4; [|intro Hx; subst; inv H13].
              assumption.
            }
          }
          repeat ssplit; [reflexivity| |assumption].
          right; exists roidx, [rqUp], ruins, ruouts.
          repeat ssplit; try assumption.
          { eapply DisjList_In_2; eauto. }
          { right; eauto. }
    Qed.

    Definition RqDownP (st: State) :=
      Forall (InMPI st.(st_msgs)) rqDowns.

    Lemma rqDown_lpush_rpush_messages_disj:
      forall rinits rins rhst routs reouts
             linits lins lhst louts leouts,
        DisjList rqDowns rinits ->
        Atomic rinits rins rhst routs reouts ->
        DisjList (oindsOf rhst) (subtreeIndsOf dtr cidx) ->
        DisjList rqDowns linits ->
        Atomic linits lins lhst louts leouts ->
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

    Hypothesis (Hoinvs: InvReachable sys step_m (liftObjInvs oinvs)).

    Lemma rqDown_lpush_rpush_unit_reducible:
      forall rinits rins rhst routs reouts
             linits lins lhst louts leouts,
        Atomic rinits rins rhst routs reouts ->
        DisjList (oindsOf rhst) (subtreeIndsOf dtr cidx) ->
        Atomic linits lins lhst louts leouts ->
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
        Atomic pinits pins phst pouts peouts ->
        SubList rqDowns peouts ->
        Atomic inits ins hst outs eouts ->
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
        Atomic inits ins hst outs eouts ->
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
            eapply rqUp_atomic with (rqUps0:= rqUps); eauto.
            { red in H4; dest; subst; discriminate. }
            { right; eauto. }
            { apply SubList_refl. }
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
            { simpl; red; intros; dest_in.
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
        Atomic rinits rins rhst routs reouts ->
        DisjList rqDowns rinits ->
        lastOIdxOf rhst = Some rloidx ->
        ~ In rloidx (subtreeIndsOf dtr cidx) ->
        Atomic linits lins lhst louts leouts ->
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
         |eapply atomic_messages_ins_ins;
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
          eapply rqUpHistory_lpush_unit_reducible with (rqUps0:= rqUps); eauto.
          { right; eauto. }
          { eapply rqUp_atomic with (rqUps0:= rqUps); eauto; try apply Hiorqs.
            { red in H1; dest; subst; discriminate. }
            { right; auto. }
            { apply SubList_refl. }
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
            eapply rqUpHistory_lpush_unit_reducible with (rqUps0:= rqUps); eauto.
            { right; eauto. }
            { eapply steps_split in H7; [|reflexivity].
              destruct H7 as [rsti [? ?]].
              eapply rqUp_atomic with (rqUps0:= rqUps); eauto.
              { red in H1; dest; subst; discriminate. }
              { right; auto. }
              { apply SubList_refl. }
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
                eapply atomic_rqDown_inits_outs_disj; eauto;
                  [|eapply steps_append; eauto].
                specialize (H0 (rqDown, rqdm)); destruct H0; auto.
                elim H0; left; reflexivity.
              }
              eapply rqDown_lpush_rpush_messages_disj
                with (rinits:= rqUps) (linits:= linits) (st1:= rsti); eauto.
              { eapply atomic_messages_ins_ins.
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
