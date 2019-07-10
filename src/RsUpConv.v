Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvMsg RqRsInvLock RqRsInvAtomic.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Lemma upLockedNew_equiv_false:
  forall (orqs1 orqs2: ORqs Msg) oidx,
    (orqs1@[oidx] >>=[[]] (fun orq => orq))@[upRq] = 
    (orqs2@[oidx] >>=[[]] (fun orq => orq))@[upRq] ->
    UpLockedNew orqs1 orqs2 oidx ->
    False.
Proof.
  unfold UpLockedNew; intros.
  destruct (orqs2@[oidx]); simpl in *; auto.
  destruct (orqs1@[oidx]); simpl in *; dest; auto.
  congruence.
Qed.

Lemma upLockedNew_weakened_false:
  forall (orqs1 orqs2: ORqs Msg) oidx,
    orqs2@[oidx] >>=[[]] (fun orq => orq)@[upRq] = None ->
    UpLockedNew orqs1 orqs2 oidx ->
    False.
Proof.
  unfold UpLockedNew; intros.
  destruct (orqs2@[oidx]); simpl in *; auto.
  dest; auto.
Qed.

(** TODO: move to [Topology.v], the one in [RqRsInvSepO.v] as well. *)
Lemma parent_parent_in_False:
  forall dtr (Hwf: WfDTree dtr) oidx1 oidx2 oidx3,
    parentIdxOf dtr oidx1 = Some oidx2 ->
    parentIdxOf dtr oidx2 = Some oidx3 ->
    In oidx3 (subtreeIndsOf dtr oidx1) ->
    False.
Proof.
  intros.
  pose proof (subtreeIndsOf_child_in Hwf _ H).
  pose proof (subtreeIndsOf_child_SubList Hwf _ H0).
  apply H3 in H2.
  pose proof (subtreeIndsOf_In_each_other_eq Hwf _ _ H1 H2); subst.
  eapply parentIdxOf_asym; eassumption.
Qed.

(** TODO: move to [RqRsInvAtomic.v] *)
Lemma upLockedNew_in_history:
  forall {oifc: OStateIfc} (sys: System oifc) st1 hst st2 oidx,
    steps step_m sys st1 hst st2 ->
    UpLockedNew (bst_orqs st1) (bst_orqs st2) oidx ->
    In oidx (oindsOf hst).
Proof.
  intros.
  destruct (in_dec idx_dec oidx (oindsOf hst)); auto.
  exfalso; eapply steps_not_in_history_no_new_uplocks; eauto.
Qed.

Section RsUpConv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (Hrrs: RqRsSys dtr sys).

  Section LockStatus.
    Variables (oinds: list IdxT) (orqs1 orqs2: ORqs Msg).

    (** Intactness of the lock state *)

    Definition UpLockIntact (oidx: IdxT) :=
      (orqs1@[oidx] >>=[[]] (fun orq => orq))@[upRq] =
      (orqs2@[oidx] >>=[[]] (fun orq => orq))@[upRq].
    
    Definition DownLockIntact (oidx: IdxT) :=
      (orqs1@[oidx] >>=[[]] (fun orq => orq))@[downRq] =
      (orqs2@[oidx] >>=[[]] (fun orq => orq))@[downRq].

    Definition ULDLIntact :=
      forall oidx,
        UpLockedNew orqs1 orqs2 oidx ->
        DownLockIntact oidx.

    Definition ULNewOrNotCovered (oidx: IdxT) :=
      UpLockedNew orqs1 orqs2 oidx \/ ~ In oidx oinds.

    Definition RqUpULNew (eouts: list (Id Msg)) :=
      forall oidx rqUp,
        RqUpMsgFrom dtr oidx rqUp ->
        In rqUp eouts ->
        UpLockedNew orqs1 orqs2 oidx.

    Definition RsDownULNew (eouts: list (Id Msg)) :=
      forall oidx rsDown,
        RsDownMsgTo dtr oidx rsDown ->
        In rsDown eouts ->
        ULNewOrNotCovered oidx.

    Definition UpLockedNewChained :=
      forall pidx orq rqiu,
        UpLockedNew orqs1 orqs2 pidx ->
        orqs2@[pidx] = Some orq -> orq@[upRq] = Some rqiu ->
        forall cidx,
          parentIdxOf dtr cidx = Some pidx ->
          edgeDownTo dtr cidx = Some rqiu.(rqi_midx_rsb) ->
          ULNewOrNotCovered cidx.

    (** Newly downlocked states *)
    
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

    (** This invariant is the only necessary condition to prove non-mergeability,
     * used in [RqRsCorrect.v] *)
    Definition RsUpDLNew (eouts: list (Id Msg)) :=
      forall oidx rsUp pidx,
        RsUpMsgFrom dtr oidx rsUp ->
        parentIdxOf dtr oidx = Some pidx ->
        In rsUp eouts ->
        DownLockedNew pidx.

    Definition DLNewBackUpLockedNew :=
      forall pidx orq rqid,
        DownLockedNew pidx ->
        orqs2@[pidx] = Some orq -> orq@[downRq] = Some rqid ->
        forall cidx,
          parentIdxOf dtr cidx = Some pidx ->
          edgeDownTo dtr cidx = Some rqid.(rqi_midx_rsb) ->
          ULNewOrNotCovered cidx.

    (** All together *)

    Definition DLOutsInv (eouts: list (Id Msg)) :=
      RqUpULNew eouts /\
      RsDownULNew eouts /\
      RqDownDLNew eouts /\
      RsUpDLNew eouts.

    Definition DLLockInv :=
      ULDLIntact /\ UpLockedNewChained /\
      DLDLNew /\ DLNewBackUpLockedNew.

    (* An orthogonal invariant, also required in proving non-mergeability *)
    Definition DLOldPreserved :=
      forall oidx rqid,
        DownLocked orqs1 oidx rqid ->
        DownLocked orqs2 oidx rqid.

    Definition DLTimeInits (inits: list (Id Msg)) :=
      forall oidx idm,
        (RqDownMsgTo dtr oidx idm \/ RsUpMsgFrom dtr oidx idm) ->
        ~ In idm inits.

    Definition DLTimeInv (inits eouts: list (Id Msg)) :=
      DLTimeInits inits ->
      DLOutsInv eouts /\ DLLockInv /\ DLOldPreserved.
    
  End LockStatus.

  (** Utility lemmas *)

  Lemma UpLockIntact_trans:
    forall orqs1 orqs2 oidx,
      UpLockIntact orqs1 orqs2 oidx ->
      forall orqs3,
        UpLockIntact orqs2 orqs3 oidx ->
        UpLockIntact orqs1 orqs3 oidx.
  Proof.
    unfold UpLockIntact; intros; congruence.
  Qed.

  Lemma UpLockIntact_UpLockedNew_1:
    forall orqs1 orqs2 oidx,
      UpLockIntact orqs1 orqs2 oidx ->
      forall orqs3,
        UpLockedNew orqs2 orqs3 oidx ->
        UpLockedNew orqs1 orqs3 oidx.
  Proof.
    unfold UpLockIntact, UpLockedNew; intros.
    destruct (orqs3@[oidx]); simpl in *; dest; auto.
    split; [assumption|].
    destruct (orqs1@[oidx]), (orqs2@[oidx]); simpl in *; auto.
    congruence.
  Qed.

  Lemma UpLockIntact_UpLockedNew_2:
    forall orqs1 orqs2 oidx,
      UpLockedNew orqs1 orqs2 oidx ->
      forall orqs3,
        UpLockIntact orqs2 orqs3 oidx ->
        UpLockedNew orqs1 orqs3 oidx.
  Proof.
    unfold UpLockIntact, UpLockedNew; intros.
    destruct (orqs2@[oidx]); simpl in *; dest; [|exfalso; auto].
    destruct (orqs1@[oidx]), (orqs3@[oidx]); simpl in *; auto.
    - split; auto; congruence.
    - split; auto; congruence.
  Qed.

  Lemma step_not_in_history_up_lock_intact:
    forall st1 oidx ridx rins routs st2 uidx,
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      uidx <> oidx ->
      UpLockIntact st1.(bst_orqs) st2.(bst_orqs) uidx.
  Proof.
    intros.
    inv H; simpl in *.
    red; intros; mred.
  Qed.

  Lemma steps_not_in_history_up_lock_intact:
    forall st1 hst st2 oidx,
      steps step_m sys st1 hst st2 ->
      ~ In oidx (oindsOf hst) ->
      UpLockIntact st1.(bst_orqs) st2.(bst_orqs) oidx.
  Proof.
    induction 1; simpl; intros; [red; reflexivity|].
    destruct lbl; try (inv H0; simpl in *; auto; fail).
    simpl in *.
    eapply UpLockIntact_trans.
    - eapply IHsteps; eauto.
    - eapply step_not_in_history_up_lock_intact.
      + apply H0.
      + auto.
  Qed.

  Lemma DownLockedNew_not_refl:
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

  Lemma DownLockedNew_equiv:
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

  Lemma DownLocked_not_DownLockedNew:
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

  Lemma DownLockedNew_DownLocked:
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

  Lemma DownLockIntact_trans:
    forall orqs1 orqs2 oidx,
      DownLockIntact orqs1 orqs2 oidx ->
      forall orqs3,
        DownLockIntact orqs2 orqs3 oidx ->
        DownLockIntact orqs1 orqs3 oidx.
  Proof.
    unfold DownLockIntact; intros; congruence.
  Qed.

  Lemma DownLockIntact_DownLockedNew_1:
    forall orqs1 orqs2 oidx,
      DownLockIntact orqs1 orqs2 oidx ->
      forall orqs3,
        DownLockedNew orqs2 orqs3 oidx ->
        DownLockedNew orqs1 orqs3 oidx.
  Proof.
    unfold DownLockIntact, DownLockedNew; intros.
    destruct (orqs3@[oidx]); simpl in *; dest; auto.
    split; [assumption|].
    destruct (orqs1@[oidx]), (orqs2@[oidx]); simpl in *; auto.
    congruence.
  Qed.

  Lemma DownLockIntact_DownLockedNew_2:
    forall orqs1 orqs2 oidx,
      DownLockedNew orqs1 orqs2 oidx ->
      forall orqs3,
        DownLockIntact orqs2 orqs3 oidx ->
        DownLockedNew orqs1 orqs3 oidx.
  Proof.
    unfold DownLockIntact, DownLockedNew; intros.
    destruct (orqs2@[oidx]); simpl in *; dest; [|exfalso; auto].
    destruct (orqs1@[oidx]), (orqs3@[oidx]); simpl in *; auto.
    - split; auto; congruence.
    - split; auto; congruence.
  Qed.

  Lemma step_not_in_history_down_lock_intact:
    forall st1 oidx ridx rins routs st2 uidx,
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      uidx <> oidx ->
      DownLockIntact st1.(bst_orqs) st2.(bst_orqs) uidx.
  Proof.
    intros.
    inv H; simpl in *.
    red; intros; mred.
  Qed.

  Lemma steps_not_in_history_down_lock_intact:
    forall st1 hst st2 oidx,
      steps step_m sys st1 hst st2 ->
      ~ In oidx (oindsOf hst) ->
      DownLockIntact st1.(bst_orqs) st2.(bst_orqs) oidx.
  Proof.
    induction 1; simpl; intros; [red; reflexivity|].
    destruct lbl; try (inv H0; simpl in *; auto; fail).
    simpl in *.
    eapply DownLockIntact_trans.
    - eapply IHsteps; eauto.
    - eapply step_not_in_history_down_lock_intact.
      + apply H0.
      + auto.
  Qed.

  Lemma DownLockedNew_not_DownLockIntact:
    forall orqs1 orqs2 oidx,
      DownLockedNew orqs1 orqs2 oidx ->
      ~ DownLockIntact orqs1 orqs2 oidx.
  Proof.
    unfold DownLockedNew, DownLockIntact; intros.
    destruct (orqs2@[oidx]); simpl in *; dest; auto.
    destruct (orqs1@[oidx]); simpl in *; auto.
    congruence.
  Qed.

  Lemma DownLockedNew_in_history:
    forall st1 hst st2 oidx,
      steps step_m sys st1 hst st2 ->
      DownLockedNew (bst_orqs st1) (bst_orqs st2) oidx ->
      In oidx (oindsOf hst).
  Proof.
    intros.
    destruct (in_dec idx_dec oidx (oindsOf hst)); auto.
    exfalso.
    eapply steps_not_in_history_down_lock_intact in H; [|eassumption].
    eapply DownLockedNew_not_DownLockIntact; eauto.
  Qed.

  Lemma DLOldPreserved_orqs_equiv:
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

  Lemma DLOldPreserved_new:
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

  Lemma DLOldPreserved_orqs_step:
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

  Lemma DLOutsInv_app:
    forall oinds orqs1 orqs2 eouts1 eouts2,
      DLOutsInv oinds orqs1 orqs2 eouts1 ->
      DLOutsInv oinds orqs1 orqs2 eouts2 ->
      DLOutsInv oinds orqs1 orqs2 (eouts1 ++ eouts2).
  Proof.
    unfold DLOutsInv; intros; dest.
    repeat ssplit.
    - red; intros; apply in_app_or in H8; destruct H8; eauto.
    - red; intros; apply in_app_or in H8; destruct H8; eauto.
    - red; intros; apply in_app_or in H9; destruct H9; eauto.
    - red; intros; apply in_app_or in H9; destruct H9; eauto.
  Qed.

  Lemma DLOutsInv_removeOnce:
    forall oinds orqs1 orqs2 eouts,
      DLOutsInv oinds orqs1 orqs2 eouts ->
      forall idm,
        DLOutsInv oinds orqs1 orqs2 (removeOnce (id_dec msg_dec) idm eouts).
  Proof.
    unfold DLOutsInv; intros; dest.
    repeat ssplit.
    - red; intros; apply removeOnce_In_2 in H4; eauto.
    - red; intros; apply removeOnce_In_2 in H4; eauto.
    - red; intros; apply removeOnce_In_2 in H5; eauto.
    - red; intros; apply removeOnce_In_2 in H5; eauto.
  Qed.
      
  Lemma DLOutsInv_removeL:
    forall oinds orqs1 orqs2 eouts,
      DLOutsInv oinds orqs1 orqs2 eouts ->
      forall msgs,
        DLOutsInv oinds orqs1 orqs2 (removeL (id_dec msg_dec) eouts msgs).
  Proof.
    unfold DLOutsInv; intros; dest.
    repeat ssplit; try assumption.
    - red; intros; apply removeL_In_2 in H4; eauto.
    - red; intros; apply removeL_In_2 in H4; eauto.
    - red; intros; apply removeL_In_2 in H5; eauto.
    - red; intros; apply removeL_In_2 in H5; eauto.
  Qed.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_msg_case.

  Ltac exfalso_wrong_msg_lock :=
    red; intros; dest_in; disc_rule_conds; solve_midx_false;
    try 
      match goal with
      | [H: UpLockedNew ?orqs ?orqs _ |- _] =>
        exfalso; eapply upLockedNew_not_refl; eauto
      | [H: DownLockedNew ?orqs ?orqs _ |- _] =>
        exfalso; eapply DownLockedNew_not_refl; eauto
      end.

  Ltac smred := repeat (simpl in *; mred).

  Hint Extern 1 (WfDTree dtr) => apply Hrrs.

  Ltac disc_RqRsDownMatch_rq :=
    repeat
      match goal with
      | [Hin: In _ ?outs, Hf: Forall _ ?outs |- _] =>
        rewrite Forall_forall in Hf; specialize (Hf _ Hin)
      end;
    try
      match goal with
      | [Hin: In _ ?outs, Hrr: RqRsDownMatch _ _ (idsOf ?outs) _ _ |- _] =>
        apply in_map with (f:= idOf) in Hin;
        let Hrri := fresh "H" in
        pose proof (RqRsDownMatch_rq_rs Hrr _ Hin) as Hrri;
        let cidx := fresh "cidx" in
        let rsUp := fresh "rsUp" in
        destruct Hrri as [cidx [rsUp ?]]; dest
      end.

  Ltac exfalso_rqDown_rsUp :=
    repeat
      match goal with
      | [H: Forall ?P _ |- _] =>
        match P with
        | context[RqDownMsgOutInv] => apply rqDown_rsUp_inv_msg in H
        end
      | [Hf: Forall (fun _ => exists _, RqDownRsUpIdx _ _ _) ?outs,
             Hin: In _ ?outs |- _] =>
        rewrite Forall_forall in Hf; specialize (Hf _ Hin);
        let oidx := fresh "oidx" in destruct Hf as [oidx ?]
      | [H1: RqDownRsUpIdx _ ?eouts ?idm, H2: RsDownMsgTo _ _ ?idm |- _] =>
        destruct H1; disc_rule_conds; solve_midx_false
      end.

  Lemma step_down_lock_time_ok:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall oidx ridx rins routs st2,
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        DLTimeInv [oidx] (bst_orqs st1) (bst_orqs st2) rins routs.
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
      repeat split; try (exfalso_wrong_msg_lock; fail).
      + red; intros; dest_in; disc_rule_conds.
        right; intro Hx; dest_in.
        apply parentIdxOf_not_eq in H32; [|apply Hrrs].
        auto.

    - (** case [ImmUp] *)
      disc_rule_conds.
      red; intros; exfalso.
      eapply H3; [|left; reflexivity].
      left; red; eauto.

    - (** case [RqFwd] *)
      disc_rule_conds.
      + (** case [RqUpUp] *)
        red; intros _.
        repeat ssplit.
        * red; repeat ssplit; try (exfalso_wrong_msg_lock; fail).
          { red; intros; dest_in; disc_rule_conds.
            red; smred; split; [discriminate|reflexivity].
          }
        * red; repeat ssplit.
          { red; intros; red; smred. }
          { red; intros.
            red in H13; destruct (idx_dec pidx (obj_idx obj)); subst; smred.
            right; intro Hx; dest_in.
            apply parentIdxOf_not_eq in H25; auto.
          }
          { red; intros.
            red in H13; destruct (idx_dec oidx (obj_idx obj)); subst; smred.
          }
          { red; intros.
            red in H13; destruct (idx_dec pidx (obj_idx obj)); subst; smred.
          }
        * apply DLOldPreserved_orqs_equiv.
          intros; smred.

      + (** case [RqUpDown] *)
        red; intros _.
        repeat ssplit.
        * red; repeat ssplit.
          { red; intros; exfalso.
            disc_RqRsDownMatch_rq; disc_rule_conds; solve_midx_false.
          }
          { red; intros; exfalso.
            disc_RqRsDownMatch_rq; disc_rule_conds; solve_midx_false.
          }
          { red; intros.
            disc_RqRsDownMatch_rq; disc_rule_conds.
            red; smred; split; [discriminate|reflexivity].
          }
          { red; intros; disc_RqRsDownMatch_rq; disc_rule_conds. }
        * red; repeat ssplit.
          { red; intros; exfalso.
            eapply upLockedNew_equiv_false; [|eassumption]; smred.
          }
          { red; intros; exfalso.
            red in H4; destruct (idx_dec pidx (obj_idx obj)); subst; smred.
          }
          { red; intros; exfalso.
            red in H4; destruct (idx_dec oidx (obj_idx obj)); subst; smred.
            disc_rule_conds; solve_midx_false.
          }
          { red; intros.
            red in H4; destruct (idx_dec pidx (obj_idx obj)); subst; smred.
            right; intro Hx; dest_in.
            apply parentIdxOf_not_eq in H25; auto.
          }
        * eapply DLOldPreserved_new; mred.

      + (** case [RqDownDown] *)
        red; intros; exfalso.
        eapply H6; [|left; reflexivity].
        left; red; eauto.

    - (** case [RsBack] *)
      good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + (** case [RsDownDown] *)
        red; intros _.
        repeat ssplit.
        * red; repeat ssplit; try (exfalso_wrong_msg_lock; fail).
          { red; intros; dest_in; disc_rule_conds.
            right; intro Hx; dest_in.
            apply parentIdxOf_not_eq in H4; auto.
          }
        * red; repeat ssplit.
          { red; intros; exfalso.
            destruct (idx_dec oidx (obj_idx obj)); subst.
            { eapply upLockedNew_weakened_false; [|eassumption]; smred. }
            { eapply upLockedNew_equiv_false; [|eassumption]; smred. }
          }
          { red; intros; exfalso.
            destruct (idx_dec pidx (obj_idx obj)); subst.
            { eapply upLockedNew_weakened_false; [|eassumption]; smred. }
            { eapply upLockedNew_equiv_false; [|eassumption]; smred. }
          }
          { red; intros; exfalso.
            red in H23; destruct (idx_dec oidx (obj_idx obj)); subst; smred.
          }
          { red; intros; exfalso.
            red in H23; destruct (idx_dec pidx (obj_idx obj)); subst; smred.
          }
        * eapply DLOldPreserved_orqs_equiv.
          intros; smred.

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
      repeat ssplit.
      + red; repeat ssplit.
        * red; intros; exfalso.
          disc_RqRsDownMatch_rq; disc_rule_conds; solve_midx_false.
        * red; intros; exfalso.
          disc_RqRsDownMatch_rq; disc_rule_conds; solve_midx_false.
        * red; intros.
          disc_RqRsDownMatch_rq; disc_rule_conds.
          red; smred; split; [discriminate|reflexivity].
        * red; intros; disc_RqRsDownMatch_rq; disc_rule_conds.
      + red; repeat ssplit.
        * red; intros; exfalso.
          destruct (idx_dec oidx (obj_idx obj)); subst.
          { eapply upLockedNew_weakened_false; [|eassumption]; smred. }
          { eapply upLockedNew_equiv_false; [|eassumption]; smred. }
        * red; intros; exfalso.
          red in H4; destruct (idx_dec pidx (obj_idx obj)); subst; smred.
        * red; intros; exfalso.
          red in H4; destruct (idx_dec oidx (obj_idx obj)); subst; smred.
          disc_rule_conds; solve_midx_false.
        * red; intros.
          red in H4; destruct (idx_dec pidx (obj_idx obj)); subst; smred.
          right; intro Hx; dest_in.
          apply parentIdxOf_not_eq in H23; auto.
      + eapply DLOldPreserved_new; mred.

  Qed.

  Lemma atomic_down_lock_time_ok:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall st1 st2,
        Reachable (steps step_m) sys st1 ->
        steps step_m sys st1 hst st2 ->
        DLTimeInv (oindsOf hst) st1.(bst_orqs) st2.(bst_orqs) inits eouts.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst;
      [inv_steps; eapply step_down_lock_time_ok; eauto|].
    inv_steps.
    specialize (IHAtomic _ _ H8 H10).

    pose proof (footprints_ok Hiorqs H0 H8) as Hftinv0.
    pose proof (footprints_ok Hiorqs H0 (reachable_steps H8 H10)) as Hftinv1.
    pose proof (downLockInv_ok Hiorqs H0 H (proj2 H1)
                               (reachable_steps H8 H10)) as Hdlinv.
    pose proof (atomic_msg_outs_ok Hiorqs Hrrs H2 H8 H10) as Hmoinv.
    
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - (** case [ImmDown] *)
      disc_rule_conds.
      inv Hmoinv; [|disc_rule_conds|].
      2: {
        simpl in *.
        apply rqDown_rsUp_inv_msg in H6; rewrite Forall_forall in H6.
        apply SubList_singleton_In in H4.
        specialize (H6 _ H4); destruct H6 as [oidx ?].
        destruct H6; disc_rule_conds; solve_midx_false.
      }
      apply SubList_singleton in H4; subst.
      rewrite removeOnce_nil; simpl.

      disc_rule_conds.
      replace (orqs +[obj_idx obj <- norq]) with orqs by meq.
      red; intros.
      specialize (IHAtomic H5); dest.
      red in H26, H27; dest.
      repeat ssplit.
      + red; repeat ssplit; try (exfalso_wrong_msg_lock; fail).
        red; intros; dest_in; disc_rule_conds.
        left; eapply H26; [|left; reflexivity].
        red; auto.
      + red; repeat ssplit; try assumption.
        * red; intros.
          specialize (H30 _ _ _ H38 H39 H40 _ H41 H42).
          destruct H30; [left; assumption|].
          right; intro Hx; icase cidx; auto.
          eapply upLockedNew_in_history in H10; [|eassumption].
          apply H14 in H10.
          eapply parent_parent_in_False
            with (dtr:= dtr) (oidx2:= obj_idx obj); eauto.
        * red; intros.
          specialize (H32 _ _ _ H38 H39 H40 _ H41 H42).
          destruct H32; [left; assumption|].
          right; intro Hx; icase cidx; auto.
          eapply DownLockedNew_in_history in H10; [|eassumption].
          eapply parent_parent_in_False
            with (dtr:= dtr) (oidx2:= obj_idx obj); eauto.
      + assumption.

    - (** case [ImmUp] *)
      disc_rule_conds.
      inv Hmoinv; [disc_rule_conds; solve_midx_false|disc_rule_conds|].
      apply SubList_singleton_In in H4.

      replace (orqs +[obj_idx obj <- norq]) with orqs by meq.
      red; intros.
      specialize (IHAtomic H21); dest.
      red in H25, H27; dest.
      repeat ssplit.

      + apply DLOutsInv_app; [apply DLOutsInv_removeOnce|].
        * red; repeat ssplit; try assumption.
          red; intros; exfalso_rqDown_rsUp.
        * red; repeat ssplit; try (exfalso_wrong_msg_lock; fail).
          red; intros; dest_in; disc_rule_conds.
          eapply H34; eauto.
          red; auto.

      + red; repeat ssplit; try assumption.
        * red; intros.
          specialize (H29 _ _ _ H36 H37 H38 _ H39 H40).
          destruct H29; [left; assumption|].
          right; intro Hx; icase cidx; auto.
          apply H27 in H36.
          eapply DownLockedNew_not_DownLockIntact; [|eassumption].
          eapply H34; [|eassumption|eassumption].
          red; auto.
        * red; intros.
          specialize (H31 _ _ _ H36 H37 H38 _ H39 H40).
          destruct H31; [left; assumption|].
          right; intro Hx; icase cidx; auto.
          (* clear Hftinv0; good_footprint_get pidx. *)
          (* disc_rule_conds. *)
          admit. (** Need to know [~ In (rqi_midx_rsb rqid) (rqi_minds_rss rqid)] *)

      + assumption.

    - (** case [RqFwd] *)
      disc_rule_conds.
      + (** case [RqUpUp] *)
        inv Hmoinv; [|disc_rule_conds|].
        2: {
          simpl in *.
          apply rqDown_rsUp_inv_msg in H23; rewrite Forall_forall in H23.
          apply SubList_singleton_In in H4.
          specialize (H23 _ H4); destruct H23 as [oidx ?].
          destruct H23; disc_rule_conds; solve_midx_false.
        }
        apply SubList_singleton in H4; subst.
        rewrite removeOnce_nil; simpl.

        disc_rule_conds.
        red; intros.
        specialize (IHAtomic H17); dest.
        red in H33, H34; dest.
        repeat ssplit.
        * red; repeat ssplit; try (exfalso_wrong_msg_lock; fail).
          red; intros; dest_in; disc_rule_conds.
          eapply UpLockIntact_UpLockedNew_1.
          { eapply steps_not_in_history_up_lock_intact; [eassumption|].
            intro Hx; apply H29 in Hx.
            eapply parent_not_in_subtree with (dtr:= dtr); eauto.
          }
          { simpl; red; intros; smred; split; [discriminate|reflexivity]. }
        * red; repeat ssplit.
          { red; intros.
            destruct (idx_dec oidx0 (obj_idx obj)); subst.
            { eapply DownLockIntact_trans.
              { eapply steps_not_in_history_down_lock_intact; [eassumption|].
                intro Hx; apply H29 in Hx.
                eapply parent_not_in_subtree with (dtr:= dtr); eauto.
              }
              { simpl; red; intros; smred. }
            }
            { eapply UpLockIntact_UpLockedNew_2
                with (orqs3:= orqs) in H43; [|red; smred].
              eapply DownLockIntact_trans with (orqs2:= orqs);
                [apply H34; assumption|].
              red; smred.
            }
          }
          { admit. }
          { admit. }
          { admit. }

        * eapply DLOldPreserved_orqs_step; [eassumption|].
          intros; smred.

      + (** case [RqUpDown] *)
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
        red in H32, H33; dest.
        repeat ssplit.
        all: admit.

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
    eapply H11; eauto.
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
    apply H6; assumption.
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
    apply DownLockedNew_DownLocked in H0.
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
    eapply DownLocked_not_DownLockedNew; eauto.
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

