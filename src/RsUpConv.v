Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvMsg RqRsInvAtomic.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Section RsUpConv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hrrs: RqRsSys dtr sys).

  Section LockStatus.
    Variables (orqs1 orqs2: ORqs Msg).

    Definition DownLockedNew (oidx: IdxT) :=
      orqs2@[oidx] >>=[False]
           (fun orq2 =>
              orq2@[downRq] <> None /\
              orqs1@[oidx] >>=[True] (fun orq1 => orq1@[downRq] = None)).

    Definition RqDownDLNew (eouts: list (Id Msg)) :=
      forall oidx rqDown pidx,
        RqDownMsgTo dtr oidx rqDown ->
        parentIdxOf dtr oidx = Some pidx ->
        In rqDown eouts ->
        DownLockedNew pidx.

    Definition DLDLNew :=
      forall oidx orq rqid,
        DownLockedNew oidx ->
        orqs2@[oidx] = Some orq -> orq@[downRq] = Some rqid ->
        forall pidx,
          parentIdxOf dtr oidx = Some pidx ->
          rsEdgeUpFrom dtr oidx = Some rqid.(rqi_midx_rsb) ->
          DownLockedNew pidx.

    Definition RsUpDLNew (eouts: list (Id Msg)) :=
      forall oidx rsUp pidx,
        RsUpMsgFrom dtr oidx rsUp ->
        parentIdxOf dtr oidx = Some pidx ->
        In rsUp eouts ->
        DownLockedNew pidx.

    Definition DLNewOuts (eouts: list (Id Msg)) :=
      RqDownDLNew eouts /\ DLDLNew /\ RsUpDLNew eouts.

    Definition DLOldPreserved :=
      forall oidx rqid,
        DownLocked orqs1 oidx rqid ->
        DownLocked orqs2 oidx rqid.

    Definition DLTimeInits (inits: list (Id Msg)) :=
      forall oidx idm,
        (RqDownMsgTo dtr oidx idm \/ RsUpMsgFrom dtr oidx idm) ->
        ~ In idm inits.

    Definition DLTimeInv (inits eouts: list (Id Msg)) :=
      DLTimeInits inits -> DLNewOuts eouts /\ DLOldPreserved.
    
  End LockStatus.

  (** Utility lemmas *)

  Lemma downLockedNew_irrefl:
    forall (orqs1 orqs2: ORqs Msg) oidx,
      (orqs1@[oidx] >>=[M.empty _] (fun orq => orq))@[downRq] =
      (orqs2@[oidx] >>=[M.empty _] (fun orq => orq))@[downRq] ->
      ~ DownLockedNew orqs1 orqs2 oidx.
  Proof.
    unfold DownLockedNew; intros.
    intro Hx.
    destruct (orqs2@[oidx]); [|auto].
    simpl in *; dest.
    destruct (orqs1@[oidx]); simpl in *; auto.
    congruence.
  Qed.

  Lemma downLockedNew_equiv:
    forall (orqs1 porqs2: ORqs Msg) oidx,
      DownLockedNew orqs1 porqs2 oidx ->
      forall (norqs2: ORqs Msg),
        (porqs2@[oidx] >>=[M.empty _] (fun orq => orq))@[downRq] =
        (norqs2@[oidx] >>=[M.empty _] (fun orq => orq))@[downRq] ->
        DownLockedNew orqs1 norqs2 oidx.
  Proof.
    unfold DownLockedNew; intros.
    destruct (porqs2@[oidx]); [|exfalso; auto].
    simpl in *; dest.
    destruct (norqs2@[oidx]); [|exfalso; auto].
    simpl in *.
    split; [congruence|auto].
  Qed.

  Lemma downLocked_not_DownLockedNew:
    forall orqs1 rqid orqs2 oidx,
      DownLocked orqs1 oidx rqid ->
      ~ DownLockedNew orqs1 orqs2 oidx.
  Proof.
    unfold DownLocked, DownLockedNew; intros.
    intro Hx.
    destruct (orqs1@[oidx]) as [orq1|]; simpl in *; auto.
    destruct (orqs2@[oidx]) as [orq2|]; simpl in *; auto.
    dest; congruence.
  Qed.

  Lemma downLockedNew_DownLocked:
    forall orqs1 orqs2 oidx,
      DownLockedNew orqs1 orqs2 oidx ->
      exists rqid, DownLocked orqs2 oidx rqid.
  Proof.
    unfold DownLocked, DownLockedNew; intros.
    destruct (orqs2@[oidx]) as [orq2|]; simpl in *; [|exfalso; auto].
    dest.
    destruct (orq2@[downRq]); eauto.
    exfalso; auto.
  Qed.

  Lemma dlOldPreserved_orqs_eq:
    forall (orqs1 orqs2: ORqs Msg),
      (forall oidx,
          (orqs1@[oidx] >>=[[]] (fun orq => orq))@[downRq] =
          (orqs2@[oidx] >>=[[]] (fun orq => orq))@[downRq]) ->
      DLOldPreserved orqs1 orqs2.
  Proof.
    unfold DLOldPreserved, DownLocked; intros.
    specialize (H oidx).
    destruct (orqs1@[oidx]); [|exfalso; auto].
    simpl in *.
    destruct (orqs2@[oidx]); simpl in *; mred.
  Qed.

  Lemma dlOldPreserved_new:
    forall (orqs: ORqs Msg) oidx orq rqid,
      (orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq] = None ->
      orq@[downRq] = Some rqid ->
      DLOldPreserved orqs (orqs +[oidx <- orq]).
  Proof.
    unfold DLOldPreserved, DownLocked; intros.
    destruct (idx_dec oidx0 oidx); subst; mred.
    destruct (orqs@[oidx]); [|exfalso; auto].
    simpl in *; exfalso; congruence.
  Qed.

  Lemma dlOldPreserved_orqs_equiv:
    forall (orqs1 porqs2: ORqs Msg),
      DLOldPreserved orqs1 porqs2 ->
      forall (norqs2: ORqs Msg),
        (forall oidx,
            (porqs2@[oidx] >>=[[]] (fun orq => orq))@[downRq] =
            (norqs2@[oidx] >>=[[]] (fun orq => orq))@[downRq]) ->
        DLOldPreserved orqs1 norqs2.
  Proof.
    unfold DLOldPreserved, DownLocked; intros.
    specialize (H oidx).
    specialize (H0 oidx).
    destruct (orqs1@[oidx]); [|exfalso; auto].
    simpl in *.
    specialize (H _ H1).
    destruct (porqs2@[oidx]); [|exfalso; auto].
    simpl in *.
    destruct (norqs2@[oidx]); simpl in *; mred.
  Qed.

  Lemma dlNewOuts_app:
    forall orqs1 orqs2 eouts1 eouts2,
      DLNewOuts orqs1 orqs2 eouts1 ->
      DLNewOuts orqs1 orqs2 eouts2 ->
      DLNewOuts orqs1 orqs2 (eouts1 ++ eouts2).
  Proof.
    unfold DLNewOuts; intros; dest.
    repeat ssplit; try assumption.
    - red; intros.
      apply in_app_or in H7; destruct H7; eauto.
    - red; intros.
      apply in_app_or in H7; destruct H7; eauto.
  Qed.

  Lemma dlNewOuts_removeOnce:
    forall orqs1 orqs2 idm eouts,
      DLNewOuts orqs1 orqs2 eouts ->
      DLNewOuts orqs1 orqs2 (removeOnce (id_dec msg_dec) idm eouts).
  Proof.
    unfold DLNewOuts; intros; dest.
    repeat ssplit; try assumption.
    - red; intros.
      apply removeOnce_In_2 in H4; eauto.
    - red; intros.
      apply removeOnce_In_2 in H4; eauto.
  Qed.

  Lemma dlNewOuts_removeL:
    forall orqs1 orqs2 msgs eouts,
      DLNewOuts orqs1 orqs2 eouts ->
      DLNewOuts orqs1 orqs2 (removeL (id_dec msg_dec) eouts msgs).
  Proof.
    unfold DLNewOuts; intros; dest.
    repeat ssplit; try assumption.
    - red; intros.
      apply removeL_In_2 in H4; eauto.
    - red; intros.
      apply removeL_In_2 in H4; eauto.
  Qed.

  Lemma dlDLNew_orqs_equiv:
    forall (orqs1 porqs2: ORqs Msg),
      DLDLNew orqs1 porqs2 ->
      forall norqs2: ORqs Msg,
        (forall oidx,
            (porqs2@[oidx] >>=[[]] (fun orq => orq))@[downRq] =
            (norqs2@[oidx] >>=[[]] (fun orq => orq))@[downRq]) ->
        DLDLNew orqs1 norqs2.
  Proof.
    red; intros.
    eapply downLockedNew_equiv; eauto.
    specialize (H0 oidx).
    rewrite H2 in H0; simpl in H0.
    rewrite H3 in H0.
    destruct (porqs2@[oidx]) as [porq2|] eqn:Hporq2; [|discriminate].
    simpl in H0.
    eapply H.
    1: {
      instantiate (1:= oidx).
      eapply downLockedNew_equiv; eauto.
      rewrite Hporq2, H2; simpl; congruence.
    }
    all: eassumption.
  Qed.

  Lemma dlNewOuts_orqs_equiv:
    forall (orqs1 porqs2: ORqs Msg) eouts,
      DLNewOuts orqs1 porqs2 eouts ->
      forall norqs2: ORqs Msg,
        (forall oidx,
            (porqs2@[oidx] >>=[[]] (fun orq => orq))@[downRq] =
            (norqs2@[oidx] >>=[[]] (fun orq => orq))@[downRq]) ->
        DLNewOuts orqs1 norqs2 eouts.
  Proof.
    unfold DLNewOuts; intros; dest.
    repeat ssplit.
    - red; intros.
      eapply downLockedNew_equiv; eauto.
    - eapply dlDLNew_orqs_equiv; eauto.
    - red; intros.
      eapply downLockedNew_equiv; eauto.
  Qed.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_msg_case.
  
  Ltac solve_RqDownDLNew_exfalso :=
    match goal with
    | |- RqDownDLNew _ _ _ =>
      red; intros; dest_in; disc_rule_conds; solve_midx_false
    end.

  Ltac solve_RsUpDLNew_exfalso :=
    match goal with
    | |- RsUpDLNew _ _ _ =>
      red; intros; dest_in; disc_rule_conds; solve_midx_false
    end.

  Lemma step_down_lock_time_ok:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall oidx ridx rins routs st2,
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        DLTimeInv (bst_orqs st1) (bst_orqs st2) rins routs.
  Proof.
    destruct Hrrs as [? [? ?]].
    intros.

    pose proof (footprints_ok Hiorqs H0 H2) as Hftinv.

    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - (** case [ImmDown] *)
      disc_rule_conds.
      replace (orqs +[obj_idx obj <- norq]) with orqs by meq.
      red; intros _.
      repeat split.
      + solve_RqDownDLNew_exfalso.
      + red; intros.
        exfalso; eapply downLockedNew_irrefl; eauto.
      + solve_RsUpDLNew_exfalso.
      + apply dlOldPreserved_orqs_eq; auto.

    - (** case [ImmUp] *)
      disc_rule_conds.
      red; intros; exfalso.
      eapply H3; [|left; reflexivity].
      left; red; eauto.

    - (** case [RqFwd] *)
      disc_rule_conds.
      + (** case [RqUpUp] *)
        red; intros _.
        repeat split.
        * solve_RqDownDLNew_exfalso.
        * red; intros.
          exfalso; eapply downLockedNew_irrefl; [|eassumption].
          repeat (simpl; mred).
          destruct (idx_dec oidx (obj_idx obj)); subst; mred.
        * solve_RsUpDLNew_exfalso.
        * apply dlOldPreserved_orqs_eq.
          intros.
          destruct (idx_dec oidx (obj_idx obj));
            subst; repeat (simpl; mred).

      + (** case [RqUpDown] *)
        red; intros _.
        repeat split.
        * red; intros.
          apply in_map with (f:= idOf) in H22.
          eapply RqRsDownMatch_rq_rs in H19; [|eassumption].
          destruct H19 as [cidx [rsUp ?]]; dest.
          disc_rule_conds.
          red; repeat (simpl; mred).
          split; [discriminate|reflexivity].
        * red; intros.
          destruct (idx_dec oidx (obj_idx obj)).
          { subst; mred; solve_midx_false. }
          { exfalso; eapply downLockedNew_irrefl; [|eassumption].
            repeat (simpl; mred).
          }
        * red; intros.
          apply in_map with (f:= idOf) in H22.
          eapply RqRsDownMatch_rq_rs in H19; [|eassumption].
          destruct H19 as [cidx [rsUp' ?]]; dest.
          disc_rule_conds; solve_midx_false.
        * eapply dlOldPreserved_new; mred.

      + (** case [RqDownDown] *)
        red; intros; exfalso.
        eapply H6; [|left; reflexivity].
        left; red; eauto.

    - (** case [RsBack] *)
      good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + (** case [RsDownDown] *)
        red; intros _.
        repeat split.
        * solve_RqDownDLNew_exfalso.
        * red; intros.
          exfalso; eapply downLockedNew_irrefl; [|eassumption].
          repeat (simpl; mred).
          destruct (idx_dec oidx (obj_idx obj)); subst; mred.
        * solve_RsUpDLNew_exfalso.
        * apply dlOldPreserved_orqs_eq.
          intros.
          destruct (idx_dec oidx (obj_idx obj));
            subst; repeat (simpl; mred).

      + (** case [RsUpDown] *)
        red; intros; exfalso.
        pose proof (RqRsDownMatch_rs_not_nil H21).
        destruct rins as [|rin rins]; [auto|].
        inv H17.
        rewrite <-H28 in H21.
        eapply RqRsDownMatch_rs_rq in H21; [|left; reflexivity].
        destruct H21 as [cidx [down ?]]; dest.
        eapply H5; [|left; reflexivity].
        right; red; eauto.

      + (** case [RsUpUp] *)
        red; intros; exfalso.
        pose proof (RqRsDownMatch_rs_not_nil H6). 
        destruct rins as [|rin rins]; [auto|].
        inv H17.
        rewrite <-H28 in H6.
        eapply RqRsDownMatch_rs_rq in H6; [|left; reflexivity].
        destruct H6 as [cidx [down ?]]; dest.
        eapply H10; [|left; reflexivity].
        right; red; eauto.

    - (** case [RsDownRqDown] *)
      disc_rule_conds.
      red; intros _.
      repeat split.
      * red; intros.
        apply in_map with (f:= idOf) in H22.
        eapply RqRsDownMatch_rq_rs in H19; [|eassumption].
        destruct H19 as [cidx [rsUp ?]]; dest.
        disc_rule_conds.
        red; repeat (simpl; mred).
        split; [discriminate|reflexivity].
      * red; intros.
        destruct (idx_dec oidx (obj_idx obj)).
        { subst; mred.
          rewrite H36 in *.
          solve_midx_false.
        }
        { exfalso; eapply downLockedNew_irrefl; [|eassumption].
          repeat (simpl; mred).
        }
      * red; intros.
        apply in_map with (f:= idOf) in H22.
        eapply RqRsDownMatch_rq_rs in H19; [|eassumption].
        destruct H19 as [cidx [rsUp' ?]]; dest.
        disc_rule_conds; solve_midx_false.
      * eapply dlOldPreserved_new; mred.
  Qed.

  Lemma atomic_down_lock_time_ok:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall st1 st2,
        Reachable (steps step_m) sys st1 ->
        steps step_m sys st1 hst st2 ->
        DLTimeInv st1.(bst_orqs) st2.(bst_orqs) inits eouts.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst;
      [inv_steps; eapply step_down_lock_time_ok; eauto|].
    inv_steps.
    specialize (IHAtomic _ _ H8 H10).

    pose proof (footprints_ok Hiorqs H0 H8) as Hftinv.
    pose proof (atomic_msg_outs_ok Hiorqs Hrrs H2 H8 H10) as Hmoinv.
    
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - (** case [ImmDown] *)
      disc_rule_conds.
      replace (orqs +[obj_idx obj <- norq]) with orqs by meq.
      red; intros.
      specialize (IHAtomic H5); dest.
      split.
      + apply dlNewOuts_app.
        * apply dlNewOuts_removeOnce; auto.
        * repeat split.
          { solve_RqDownDLNew_exfalso. }
          { apply H6. }
          { solve_RsUpDLNew_exfalso. }
      + assumption.

    - (** case [ImmUp] *)
      disc_rule_conds.
      replace (orqs +[obj_idx obj <- norq]) with orqs by meq.
      red; intros.
      specialize (IHAtomic H5); dest.
      split.
      + apply dlNewOuts_app.
        * apply dlNewOuts_removeOnce; auto.
        * red; repeat ssplit.
          { solve_RqDownDLNew_exfalso. }
          { apply H6. }
          { red; intros; dest_in; disc_rule_conds.
            red in H6; dest.
            eapply H6 with (rqDown:= (rqFrom, rqm)).
            { red; eauto. }
            { assumption. }
            { apply SubList_singleton_In; assumption. }
          }
      + assumption.

    - (** case [RqFwd] *)
      disc_rule_conds.
      + (** case [RqUpUp] *)
        red; intros.
        specialize (IHAtomic H17); dest.
        split.
        * apply dlNewOuts_app.
          { apply dlNewOuts_removeOnce.
            eapply dlNewOuts_orqs_equiv; eauto.
            intros; repeat (simpl; mred).
          }
          { repeat split.
            { solve_RqDownDLNew_exfalso. }
            { eapply dlDLNew_orqs_equiv; [apply H23|].
              intros; repeat (simpl; mred).
            }
            { solve_RsUpDLNew_exfalso. }
          }
        * eapply dlOldPreserved_orqs_equiv; [eassumption|].
          intros; repeat (simpl; mred).

      + (** case [RqUpDown] *)
        (* .. Ltac? *)
        inv Hmoinv; [|disc_rule_conds|].
        2: {
          apply rqDown_rsUp_inv_msg in H17; rewrite Forall_forall in H17.
          apply SubList_singleton_In in H4.
          specialize (H17 _ H4); destruct H17 as [oidx ?].
          destruct H17; disc_rule_conds; solve_midx_false.
        }
        apply SubList_singleton in H4; subst.
        rewrite removeOnce_nil; simpl.
        disc_rule_conds.

        red; intros.
        specialize (IHAtomic H6); dest.
        red in H32; dest.

        split.
        * repeat split.
          { (** TODO: need to substitute [bst_orqs st1] to [orqs]
             * by proving a lemma that relates [DLNewOuts] and [steps] *)
            admit.
          }
          { red; intros.
            destruct (idx_dec oidx (obj_idx obj)).
            { subst; mred; solve_midx_false. }
            { admit. }
          }
          { red; intros; exfalso.
            apply in_map with (f:= idOf) in H39.
            eapply RqRsDownMatch_rq_rs in H23; [|eassumption].
            destruct H23 as [cidx [rsUp' ?]]; dest.
            disc_rule_conds; solve_midx_false.
          }
        * admit.

      + (** case [RqDownDown] *)
        admit.

    - (** case [RsBack] *)
      admit.

    - (** case [RsDownRqDown] *)
      admit.

  Admitted.

End RsUpConv.

Section Corollaries.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hrrs: RqRsSys dtr sys).

  Lemma extAtomic_DLTimeInits:
    forall inits trs eouts,
      ExtAtomic sys msg_dec inits trs eouts ->
      DLTimeInits dtr inits.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    inv H2.
    red; intros.
    intro Hx.
    apply in_map with (f:= idOf) in Hx.
    apply H3 in Hx.
    apply Hrrs in Hx.
    destruct Hx as [eoidx ?].
    destruct H2.
    - disc_msg_case; solve_midx_false.
    - disc_msg_case; solve_midx_false.
  Qed.

  Corollary extAtomic_down_lock_time_ok:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall trs st2,
        steps step_m sys st1 trs st2 ->
        forall inits eouts,
          ExtAtomic sys msg_dec inits trs eouts ->
          forall cidx rsUp pidx,
            RsUpMsgFrom dtr cidx rsUp ->
            parentIdxOf dtr cidx = Some pidx ->
            In rsUp eouts ->
            DownLockedNew st1.(bst_orqs) st2.(bst_orqs) pidx.
  Proof.
    intros.
    pose proof (extAtomic_DLTimeInits H1).
    inv H1.
    eapply atomic_down_lock_time_ok in H7; eauto.
    specialize (H7 H5); dest.
    red in H1; dest.
    eapply H9; eauto.
  Qed.

  Corollary extAtomic_rsUp_down_lock_preserved:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall trs st2,
        steps step_m sys st1 trs st2 ->
        forall inits eouts,
          ExtAtomic sys msg_dec inits trs eouts ->
          forall oidx rqid,
            DownLocked st1.(bst_orqs) oidx rqid ->
            DownLocked st2.(bst_orqs) oidx rqid.
  Proof.
    intros.
    pose proof (extAtomic_DLTimeInits H1).
    inv H1.
    eapply atomic_down_lock_time_ok in H5; eauto.
    specialize (H5 H3); dest.
    apply H5; assumption.
  Qed.

  Lemma extAtomic_multi_rsUps_not_diverged_sub:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall inits1 trs1 eouts1,
        ExtAtomic sys msg_dec inits1 trs1 eouts1 ->
        forall trss inits2 trs2 eouts2 st2,
          steps step_m sys st1 (trs2 ++ List.concat trss ++ trs1) st2 ->
          ExtAtomic sys msg_dec inits2 trs2 eouts2 ->
          Forall (AtomicEx msg_dec) trss ->
          Forall (Transactional sys msg_dec) trss ->
          forall cidx1 rsUp1 cidx2 rsUp2 pidx,
            RsUpMsgFrom dtr cidx1 rsUp1 ->
            parentIdxOf dtr cidx1 = Some pidx ->
            RsUpMsgFrom dtr cidx2 rsUp2 ->
            parentIdxOf dtr cidx2 = Some pidx ->
            In rsUp1 eouts1 -> In rsUp2 eouts2 -> False.
  Proof.
    intros.
    rewrite app_assoc in H1.
    eapply steps_split in H1; [|reflexivity].
    destruct H1 as [sti1 [? ?]].
    eapply extAtomic_down_lock_time_ok with (rsUp:= rsUp1) in H0; eauto.
    apply downLockedNew_DownLocked in H0.
    destruct H0 as [rqid ?].

    eapply steps_split in H11; [|reflexivity].
    destruct H11 as [sti2 [? ?]].
    assert (DownLocked (bst_orqs sti2) pidx rqid).
    { assert (Reachable (steps step_m) sys sti1) by eauto.
      clear -Hiorqs Hrrs H0 H3 H4 H11 H13.
      generalize dependent sti2.
      generalize dependent trss.
      induction trss as [|trs trss]; simpl; intros; [inv_steps; assumption|].
      inv H3; inv H4.
      eapply steps_split in H11; [|reflexivity].
      destruct H11 as [stii [? ?]].
      specialize (IHtrss H5 H6 _ H).
      pose proof (atomic_Transactional_ExtAtomic H2 H3).
      destruct H4 as [einits [eouts ?]].
      eapply extAtomic_rsUp_down_lock_preserved with (st1:= stii); eauto.
    }

    eapply extAtomic_down_lock_time_ok
      with (rsUp:= rsUp2) (st1:= sti2) (st2:= st2) in H2; eauto;
      [|eapply reachable_steps; [|eassumption]; eauto].
    eapply downLocked_not_DownLockedNew; eauto.
  Qed.

  Lemma extAtomic_multi_rsUps_not_diverged_gt:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall trss st2,
        steps step_m sys st1 (List.concat trss) st2 ->
        Forall (AtomicEx msg_dec) trss ->
        Forall (Transactional sys msg_dec) trss ->
        forall n1 inits1 trs1 eouts1 n2 inits2 trs2 eouts2,
          n1 > n2 ->
          nth_error trss n1 = Some trs1 ->
          nth_error trss n2 = Some trs2 ->
          ExtAtomic sys msg_dec inits1 trs1 eouts1 ->
          ExtAtomic sys msg_dec inits2 trs2 eouts2 ->
          forall cidx1 rsUp1 cidx2 rsUp2 pidx,
            RsUpMsgFrom dtr cidx1 rsUp1 ->
            parentIdxOf dtr cidx1 = Some pidx ->
            RsUpMsgFrom dtr cidx2 rsUp2 ->
            parentIdxOf dtr cidx2 = Some pidx ->
            In rsUp1 eouts1 -> In rsUp2 eouts2 -> False.
  Proof.
    intros.
    assert (exists ptrss itrss ntrss,
               trss = ntrss ++ trs2 :: itrss ++ trs1 :: ptrss) as Htrss.
    { apply nth_error_split in H5.
      destruct H5 as [ntrss [ptrss2 ?]]; dest; subst.
      rewrite nth_error_app2 in H4; [|omega].
      apply nth_error_split in H4.
      destruct H4 as [ntrss1 [ptrss ?]]; dest; subst.
      destruct ntrss1; [simpl in *; omega|].
      simpl in *; inv H4.
      do 3 eexists; reflexivity.
    }
    destruct Htrss as [ptrss [itrss [ntrss ?]]]; subst.

    repeat (rewrite concat_app in H0; simpl in H0).
    eapply steps_split in H0; [|reflexivity].
    destruct H0 as [sti2 [? ?]].
    do 2 rewrite app_assoc in H0.
    eapply steps_split in H0; [|reflexivity].
    destruct H0 as [sti1 [? ?]].
    rewrite <-app_assoc in H15.

    eapply extAtomic_multi_rsUps_not_diverged_sub
      with (trs1:= trs1) (trs2:= trs2) (rsUp1:= rsUp1) (rsUp2:= rsUp2)
           (st1:= sti1) (st2:= sti2); eauto.
    - apply Forall_app_inv in H1; dest.
      inv H16.
      apply Forall_app_inv in H20; dest.
      assumption.
    - apply Forall_app_inv in H2; dest.
      inv H16.
      apply Forall_app_inv in H20; dest.
      assumption.
  Qed.

  Lemma extAtomic_multi_rsUps_not_diverged:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall trss st2,
        steps step_m sys st1 (List.concat trss) st2 ->
        Forall (AtomicEx msg_dec) trss ->
        Forall (Transactional sys msg_dec) trss ->
        forall n1 inits1 trs1 eouts1 n2 inits2 trs2 eouts2,
          n1 <> n2 ->
          nth_error trss n1 = Some trs1 ->
          nth_error trss n2 = Some trs2 ->
          ExtAtomic sys msg_dec inits1 trs1 eouts1 ->
          ExtAtomic sys msg_dec inits2 trs2 eouts2 ->
          forall cidx1 rsUp1 cidx2 rsUp2 pidx,
            RsUpMsgFrom dtr cidx1 rsUp1 ->
            parentIdxOf dtr cidx1 = Some pidx ->
            RsUpMsgFrom dtr cidx2 rsUp2 ->
            parentIdxOf dtr cidx2 = Some pidx ->
            In rsUp1 eouts1 -> In rsUp2 eouts2 -> False.
  Proof.
    intros.
    destruct (lt_eq_lt_dec n1 n2) as [[|]|]; [|auto|].
    - eapply extAtomic_multi_rsUps_not_diverged_gt
        with (trs1:= trs2) (trs2:= trs1) (rsUp1:= rsUp2) (rsUp2:= rsUp1); eauto.
    - eapply extAtomic_multi_rsUps_not_diverged_gt
        with (trs1:= trs1) (trs2:= trs2) (rsUp1:= rsUp1) (rsUp2:= rsUp2); eauto.
  Qed.

End Corollaries.

