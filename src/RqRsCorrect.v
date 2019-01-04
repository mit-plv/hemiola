Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant.
Require Import Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsInv.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

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
        exists rqUp rsbTo,
          OUpLockedTo st2.(bst_orqs) oidx rsbTo /\
          rqEdgeUpFrom dtr oidx = Some rqUp /\
          length (findQ rqUp st2.(bst_msgs)) = 1.
  Proof.
    intros.
    destruct Hrrs as [? [? ?]].

    assert (LockInv dtr sys st2) as Hlock.
    { apply lockInv_ok; auto.
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
      apply SubList_singleton in H0; subst; simpl in *.
      rewrite H2 in H27; discriminate.
    - exfalso; disc_rule_conds.
      apply SubList_singleton in H0; subst; simpl in *.
      rewrite H2 in H25; discriminate.

    - disc_rule_conds.
      + (** The only non-"exfalso" case *)
        apply SubList_singleton in H0; subst; simpl in *.
        good_locking_get obj.

        (* TODO: better to have a discharger for [LockInv]? *)
        red in H0; mred; simpl in H0.
        rewrite H25 in H0.
        destruct H0 as [rqUp' [down [pidx ?]]]; dest.
        (* TODO ends here *)

        disc_footprints_ok.
        disc_rule_conds.

        split; [|split].
        * exists cidx, i.
          repeat split; try assumption.
        * reflexivity.
        * exists rqUp', (rqi_midx_rsb rqi).
          repeat split.
          { red; mred; simpl.
            exists rqi; split; auto.
          }
          { clear -H19.
            rewrite findQ_In_enqMP in *.
            rewrite app_length in H19; simpl in H19.
            rewrite app_length; simpl.
            omega.
          }
      + exfalso; disc_rule_conds.
        apply SubList_singleton_In in H0.
        red in H23; destruct H23 as [upCIdx ?]; dest.
        eapply RqRsDownMatch_rq_In in H23; [|apply in_map; eassumption].
        destruct H23 as [cidx ?]; dest.
        pose proof (rqrsDTree_rqUp_down_not_eq H3 _ _ H7 H27); auto.
      + exfalso; disc_rule_conds.
        apply SubList_singleton_In in H0.
        red in H23; destruct H23 as [upCIdx ?]; dest.
        eapply RqRsDownMatch_rq_In in H9; [|apply in_map; eassumption].
        destruct H9 as [cidx ?]; dest.
        pose proof (rqrsDTree_rqUp_down_not_eq H3 _ _ H7 H23); auto.

    - exfalso; disc_rule_conds.
      + apply SubList_singleton in H0; subst; simpl in *.
        rewrite H2 in H27; discriminate.
      + apply SubList_singleton in H0; subst; simpl in *.
        rewrite H2 in H27; discriminate.
    - exfalso; disc_rule_conds.
      apply SubList_singleton_In in H0.
      red in H23; destruct H23 as [upCIdx ?]; dest.
      eapply RqRsDownMatch_rq_In in H27; [|apply in_map; eassumption].
      destruct H27 as [cidx ?]; dest.
      pose proof (rqrsDTree_rqUp_down_not_eq H3 _ _ H7 H31); auto.
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
  
  Lemma rqUp_lbl_reducible:
    forall oidxTo rqUps oidx1 ridx1 rins1 routs1,
      RqUpMsgs dtr oidxTo rqUps ->
      SubList rqUps routs1 ->
      forall oidx2 ridx2 rins2 routs2,
        DisjList rins2 routs1 ->
        Reducible
          sys [RlblInt oidx2 ridx2 rins2 routs2;
                 RlblInt oidx1 ridx1 rins1 routs1]
          [RlblInt oidx1 ridx1 rins1 routs1;
             RlblInt oidx2 ridx2 rins2 routs2].
  Proof.
    intros.
    apply internal_commutes.
  Admitted.
  
  Lemma rqUp_lpush_lbl:
    forall pinits pins phst pouts peouts,
      Atomic msg_dec pinits pins phst pouts peouts ->
      forall oidxTo rqUps,
        RqUpMsgs dtr oidxTo rqUps ->
        SubList rqUps peouts ->
        forall oidx ridx rins routs,
          DisjList rins peouts ->
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
      DisjList inits peouts ->
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
