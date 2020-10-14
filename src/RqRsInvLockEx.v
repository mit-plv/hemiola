Require Import PeanoNat Compare_dec Lia List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvMsg RqRsInvLock RqRsInvAtomic.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Lemma upLockedNew_equiv_false:
  forall `{dv: DecValue} (orqs1 orqs2: ORqs Msg) oidx,
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
  forall `{dv: DecValue} (orqs1 orqs2: ORqs Msg) oidx,
    orqs2@[oidx] >>=[[]] (fun orq => orq)@[upRq] = None ->
    UpLockedNew orqs1 orqs2 oidx ->
    False.
Proof.
  unfold UpLockedNew; intros.
  destruct (orqs2@[oidx]); simpl in *; auto.
  dest; auto.
Qed.

Lemma upLockedNew_in_history:
  forall `{dv: DecValue} `{oifc: OStateIfc} (sys: System) st1 hst st2 oidx,
    steps step_m sys st1 hst st2 ->
    UpLockedNew (st_orqs st1) (st_orqs st2) oidx ->
    In oidx (oindsOf hst).
Proof.
  intros.
  destruct (in_dec idx_dec oidx (oindsOf hst)); auto.
  exfalso; eapply steps_not_in_history_no_new_uplocks; eauto.
Qed.

Section RqRsInvLockEx.
  Context `{dv: DecValue} `{oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System).
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (oinvs: IdxT -> ObjInv)
             (Hrrs: RqRsSys dtr sys oinvs).

  Section LockStatus.
    Variables (orqs1 orqs2: ORqs Msg).

    (** Intactness of the lock state *)

    Definition DownLockIntact (oidx: IdxT) :=
      (orqs1@[oidx] >>=[[]] (fun orq => orq))@[downRq] =
      (orqs2@[oidx] >>=[[]] (fun orq => orq))@[downRq].

    Definition DLIntactAll :=
      forall oidx, DownLockIntact oidx.

    Definition DLIntactBound (oidx: IdxT) :=
      forall soidx,
        In soidx (subtreeIndsOf dtr oidx) ->
        DownLockIntact soidx.

    Definition RqUpULNew (eouts: list (Id Msg)) :=
      forall oidx rqUp,
        RqUpMsgFrom dtr oidx rqUp ->
        In rqUp eouts ->
        DLIntactAll.

    Definition RsDownULNew (eouts: list (Id Msg)) :=
      forall oidx rsDown,
        RsDownMsgTo dtr oidx rsDown ->
        In rsDown eouts ->
        DLIntactBound oidx.

    (** Newly downlocked states *)

    Definition DownLockedNew (oidx: IdxT) :=
      orqs2@[oidx] >>=[False]
           (fun orq2 =>
              orq2@[downRq] <> None /\
              orqs1@[oidx] >>=[True] (fun orq1 => orq1@[downRq] = None)).

    Inductive DLNewRec: IdxT -> Prop :=
    | DLNewRecIntro:
        forall oidx,
          DownLockedNew oidx ->
          (forall orq rqid pidx,
              orqs2@[oidx] = Some orq ->
              orq@[downRq] = Some rqid ->
              parentIdxOf dtr oidx = Some pidx ->
              rsEdgeUpFrom dtr oidx = rqid.(rqi_midx_rsb) ->
              DLNewRec pidx) ->
          DLNewRec oidx.

    Definition DownLockNotTo (oidx: IdxT) (midx: IdxT) :=
      forall orq rqid,
        orqs2@[oidx] = Some orq ->
        orq@[downRq] = Some rqid ->
        rqid.(rqi_midx_rsb) <> Some midx.

    Definition RqDownDLNew (eouts: list (Id Msg)) :=
      forall oidx rqDown pidx,
        RqDownMsgTo dtr oidx rqDown ->
        parentIdxOf dtr oidx = Some pidx ->
        In rqDown eouts ->
        DLNewRec pidx /\ DownLockNotTo pidx (idOf rqDown).

    (** This invariant is the only necessary condition to prove nonmergeability,
     * used in [RqRsCorrect.v] *)
    Definition RsUpDLNew (eouts: list (Id Msg)) :=
      forall oidx rsUp pidx,
        RsUpMsgFrom dtr oidx rsUp ->
        parentIdxOf dtr oidx = Some pidx ->
        In rsUp eouts ->
        DLNewRec pidx.

    Definition DLNewBackUpLockedNew :=
      forall pidx orq rqid,
        DownLockedNew pidx ->
        orqs2@[pidx] = Some orq -> orq@[downRq] = Some rqid ->
        forall cidx,
          parentIdxOf dtr cidx = Some pidx ->
          edgeDownTo dtr cidx = rqid.(rqi_midx_rsb) ->
          DLIntactBound cidx.

    (** All together *)

    Definition DLOutsInv (eouts: list (Id Msg)) :=
      RqUpULNew eouts /\
      RsDownULNew eouts /\
      RqDownDLNew eouts /\
      RsUpDLNew eouts.

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
      DLOutsInv eouts /\ DLNewBackUpLockedNew /\ DLOldPreserved.

  End LockStatus.

  (** Utility lemmas *)

  Ltac smred := repeat (simpl in *; mred).

  Lemma DLIntactAll_trans:
    forall orqs1 orqs2,
      DLIntactAll orqs1 orqs2 ->
      forall orqs3,
        DLIntactAll orqs2 orqs3 ->
        DLIntactAll orqs1 orqs3.
  Proof.
    unfold DLIntactAll; intros.
    specialize (H oidx).
    specialize (H0 oidx).
    congruence.
  Qed.

  Lemma DLIntactAll_DLIntactBound:
    forall orqs1 orqs2,
      DLIntactAll orqs1 orqs2 ->
      forall oidx, DLIntactBound orqs1 orqs2 oidx.
  Proof.
    unfold DLIntactAll, DLIntactBound; intros; auto.
  Qed.

  Lemma DLIntactBound_refl:
    forall orqs1 orqs2 oidx,
      (forall oidx, DownLockIntact orqs1 orqs2 oidx) ->
      DLIntactBound orqs1 orqs2 oidx.
  Proof.
    unfold DLIntactBound; intros; auto.
  Qed.

  Lemma DLIntactBound_step_eq:
    forall orqs oidx orq,
      DownLockIntact orqs (orqs +[oidx <- orq]) oidx ->
      DLIntactBound orqs (orqs +[oidx <- orq]) oidx.
  Proof.
    unfold DLIntactBound; intros.
    red; intros.
    apply subtreeIndsOf_composed in H0; [|apply Hrrs].
    destruct H0.
    - subst; red in H; smred.
    - destruct H0 as [cidx [? ?]].
      assert (soidx <> oidx).
      { apply parent_not_in_subtree in H0; [|apply Hrrs].
        intro Hx; subst; auto.
      }
      smred.
  Qed.

  Lemma DLIntactBound_trans:
    forall orqs1 orqs2 oidx,
      DLIntactBound orqs1 orqs2 oidx ->
      forall orqs3,
        DLIntactBound orqs2 orqs3 oidx ->
        DLIntactBound orqs1 orqs3 oidx.
  Proof.
    unfold DLIntactBound; intros.
    specialize (H _ H1).
    specialize (H0 _ H1).
    congruence.
  Qed.

  Lemma DLIntactBound_step_neq:
    forall orqs oidx orq otidx,
      ~ In oidx (subtreeIndsOf dtr otidx) ->
      DLIntactBound orqs (orqs +[oidx <- orq]) otidx.
  Proof.
    unfold DLIntactBound; intros.
    red; intros.
    assert (oidx <> soidx) by (intro Hx; subst; auto).
    smred.
  Qed.

  Lemma DLIntactBound_child:
    forall orqs1 orqs2 oidx,
      DLIntactBound orqs1 orqs2 oidx ->
      forall cidx,
        parentIdxOf dtr cidx = Some oidx ->
        DLIntactBound orqs1 orqs2 cidx.
  Proof.
    unfold DLIntactBound; intros.
    eapply subtreeIndsOf_child_SubList in H1;
      try apply Hrrs; eauto.
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
      DownLockIntact st1.(st_orqs) st2.(st_orqs) uidx.
  Proof.
    intros.
    inv H; simpl in *.
    red; intros; mred.
  Qed.

  Lemma steps_not_in_history_down_lock_intact:
    forall st1 hst st2 oidx,
      steps step_m sys st1 hst st2 ->
      ~ In oidx (oindsOf hst) ->
      DownLockIntact st1.(st_orqs) st2.(st_orqs) oidx.
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
      DownLockedNew (st_orqs st1) (st_orqs st2) oidx ->
      In oidx (oindsOf hst).
  Proof.
    intros.
    destruct (in_dec idx_dec oidx (oindsOf hst)); auto.
    exfalso.
    eapply steps_not_in_history_down_lock_intact in H; [|eassumption].
    eapply DownLockedNew_not_DownLockIntact; eauto.
  Qed.

  Lemma DLNewRec_orqs_step_intact:
    forall orqs1 orqs2 cidx,
      DLNewRec orqs1 orqs2 cidx ->
      forall oidx orq,
        oidx <> cidx -> ~ In cidx (subtreeIndsOf dtr oidx) ->
        DLNewRec orqs1 (orqs2 +[oidx <- orq]) cidx.
  Proof.
    induction 1; intros.
    constructor.
    - eapply DownLockIntact_DownLockedNew_2; [eassumption|].
      red; smred.
    - intros; smred.
      eapply H1; eauto.
      + intro Hx; subst.
        elim H3.
        apply subtreeIndsOf_child_in; [apply Hrrs|]; auto.
      + intro Hx; elim H3.
        eapply inside_child_in; [apply Hrrs|..]; eauto.
  Qed.

  (* Lemma DLNewRec_orqs_step_remove_silent: *)
  (*   forall orqs1 orqs2 cidx, *)
  (*     DLNewRec orqs1 orqs2 cidx -> *)
  (*     forall oidx porq, *)
  (*       oidx <> cidx -> *)
  (*       In cidx (subtreeIndsOf dtr oidx) -> *)
  (*       orqs2@[oidx] = Some porq -> *)
  (*       (porq@[downRq] >>=[True] (fun rqid => rqid.(rqi_midx_rsb) = None)) -> *)
  (*       forall norq, *)
  (*         (norq@[downRq] >>=[True] (fun rqid => rqid.(rqi_midx_rsb) = None)) -> *)
  (*         DLNewRec orqs1 (orqs2 +[oidx <- norq]) cidx. *)
  (* Proof. *)
  (* Qed. *)

  Lemma DLNewBackUpLockedNew_orqs_step_remove:
    forall orqs1 orqs2,
      DLNewBackUpLockedNew orqs1 orqs2 ->
      forall oidx,
        DownLockedNew orqs1 orqs2 oidx ->
        forall norq,
          norq@[downRq] = None ->
          DLNewBackUpLockedNew orqs1 (orqs2 +[oidx <- norq]).
  Proof.
    intros.
    red; intros.
    red; intros.
    destruct (idx_dec oidx pidx); subst; smred.
    eapply DownLockIntact_DownLockedNew_2 in H2; [|red; smred].
    destruct (idx_dec soidx oidx); subst.
    - exfalso.
      eapply DownLockedNew_not_DownLockIntact; [apply H0|].
      eapply H; eauto.
    - apply DownLockIntact_trans with (orqs2:= orqs2).
      + eapply H; eauto.
      + red; smred.
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

  Lemma DLOldPreserved_trans:
    forall orqs1 orqs2,
      DLOldPreserved orqs1 orqs2 ->
      forall orqs3,
        DLOldPreserved orqs2 orqs3 ->
        DLOldPreserved orqs1 orqs3.
  Proof.
    unfold DLOldPreserved; intros; eauto.
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

  Lemma DLOldPreserved_remove:
    forall orqs1 orqs2,
      DLOldPreserved orqs1 orqs2 ->
      forall roidx norq,
        DownLockedNew orqs1 orqs2 roidx ->
        norq@[downRq] = None ->
        DLOldPreserved orqs1 (orqs2 +[roidx <- norq]).
  Proof.
    unfold DLOldPreserved; intros.
    destruct (idx_dec oidx roidx); subst.
    - exfalso; red in H0, H2.
      destruct (orqs2@[roidx]) as [orq2|]; [|auto]; simpl in *; dest.
      destruct (orqs1@[roidx]); [|auto]; simpl in *; congruence.
    - red; smred.
      apply H; auto.
  Qed.

  Lemma DLOutsInv_app:
    forall orqs1 orqs2 eouts1 eouts2,
      DLOutsInv orqs1 orqs2 eouts1 ->
      DLOutsInv orqs1 orqs2 eouts2 ->
      DLOutsInv orqs1 orqs2 (eouts1 ++ eouts2).
  Proof.
    unfold DLOutsInv; intros; dest.
    repeat ssplit.
    - red; intros; apply in_app_or in H8; destruct H8; eauto.
    - red; intros; apply in_app_or in H8; destruct H8; eauto.
    - red; intros; apply in_app_or in H9; destruct H9; eauto.
    - red; intros; apply in_app_or in H9; destruct H9; eauto.
  Qed.

  Lemma DLOutsInv_removeOnce:
    forall orqs1 orqs2 eouts,
      DLOutsInv orqs1 orqs2 eouts ->
      forall idm,
        DLOutsInv orqs1 orqs2 (removeOnce (id_dec msg_dec) idm eouts).
  Proof.
    unfold DLOutsInv; intros; dest.
    repeat ssplit.
    - red; intros; apply removeOnce_In_2 in H4; eauto.
    - red; intros; apply removeOnce_In_2 in H4; eauto.
    - red; intros; apply removeOnce_In_2 in H5; eauto.
    - red; intros; apply removeOnce_In_2 in H5; eauto.
  Qed.

  Lemma DLOutsInv_removeL:
    forall orqs1 orqs2 eouts,
      DLOutsInv orqs1 orqs2 eouts ->
      forall msgs,
        DLOutsInv orqs1 orqs2 (removeL (id_dec msg_dec) eouts msgs).
  Proof.
    unfold DLOutsInv; intros; dest.
    repeat ssplit; try assumption.
    - red; intros; apply removeL_In_2 in H4; eauto.
    - red; intros; apply removeL_In_2 in H4; eauto.
    - red; intros; apply removeL_In_2 in H5; eauto.
    - red; intros; apply removeL_In_2 in H5; eauto.
  Qed.

  Lemma DLOutsInv_nil:
    forall orqs1 orqs2, DLOutsInv orqs1 orqs2 nil.
  Proof.
    intros; red; intros.
    repeat ssplit.
    - red; intros; elim H0.
    - red; intros; elim H0.
    - red; intros; elim H1.
    - red; intros; elim H1.
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
        DLTimeInv (st_orqs st1) (st_orqs st2) rins routs.
  Proof.
    destruct Hrrs as [? [? ?]].
    intros.

    pose proof (footprints_ok Hiorqs H0 H2) as Hftinv.

    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - (** case [ImmDown] *)
      disc_rule_conds.
      + replace (orqs +[obj_idx obj <- norq]) with orqs by meq.
        red; intros _.
        repeat ssplit.
        * red; repeat ssplit; try (red; intros; dest_in; fail).
        * red; repeat split.
        * red; intros; assumption.
      + replace (orqs +[obj_idx obj <- norq]) with orqs by meq.
        red; intros _.
        repeat ssplit.
        * red; repeat ssplit; try (exfalso_wrong_msg_lock; fail).
          red; intros.
          apply DLIntactBound_refl.
          intros; reflexivity.
        * red; repeat split; try (exfalso_wrong_msg_lock; fail).
        * red; intros; assumption.

    - (** case [ImmUp] *)
      disc_rule_conds.
      red; intros; exfalso.
      eapply H3; [|left; reflexivity].
      left; red; eauto.

    - (** case [RqFwd] *)
      disc_rule_conds.
      + (** case [RqUpUp-silent] *)
        red; intros _.
        repeat ssplit.
        * red; repeat ssplit; try (exfalso_wrong_msg_lock; fail).
          red; intros; dest_in; disc_rule_conds.
          red; intros; red; smred.
        * red; intros.
          red; intros.
          red in H6; destruct (idx_dec pidx (obj_idx obj)); subst; smred.
        * apply DLOldPreserved_orqs_equiv.
          intros; smred.

      + (** case [RqUpUp] *)
        red; intros _.
        repeat ssplit.
        * red; repeat ssplit; try (exfalso_wrong_msg_lock; fail).
          red; intros; dest_in; disc_rule_conds.
          red; intros; red; smred.
        * red; intros.
          red; intros.
          red in H13; destruct (idx_dec pidx (obj_idx obj)); subst; smred.
        * apply DLOldPreserved_orqs_equiv.
          intros; smred.

      + (** case [RqUpDown-silent] *)
        red; intros _.
        repeat ssplit.
        * red; repeat ssplit.
          { red; intros; exfalso.
            disc_RqRsDownMatch_rq; disc_rule_conds; solve_midx_false.
          }
          { red; intros; exfalso.
            disc_RqRsDownMatch_rq; disc_rule_conds; solve_midx_false.
          }
          { red; intros; split.
            { disc_RqRsDownMatch_rq; disc_rule_conds.
              constructor.
              { red; smred; split; [discriminate|reflexivity]. }
              { intros; smred.
                rewrite H38 in *.
                apply parentIdxOf_Some in H24; [|apply H].
                dest; congruence.
              }
            }
            { disc_RqRsDownMatch_rq; disc_rule_conds.
              red; intros; smred.
              intro Hx; rewrite Hx in *.
              disc_rule_conds; auto.
            }
          }
          { red; intros; disc_RqRsDownMatch_rq; disc_rule_conds. }
        * red; repeat ssplit.
          red; intros.
          red in H3; destruct (idx_dec pidx (obj_idx obj)); subst; smred.
          eapply DLIntactBound_step_neq; eauto.
          apply parent_not_in_subtree; auto.
        * eapply DLOldPreserved_new; mred.

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
          { red; intros; split.
            { disc_RqRsDownMatch_rq; disc_rule_conds.
              constructor.
              { red; smred; split; [discriminate|reflexivity]. }
              { intros; smred.
                rewrite H38 in *; solve_midx_false.
              }
            }
            { disc_RqRsDownMatch_rq; disc_rule_conds.
              red; intros; smred.
              intro Hx; rewrite Hx in *.
              disc_rule_conds; auto.
            }
          }
          { red; intros; disc_RqRsDownMatch_rq; disc_rule_conds. }
        * red; repeat ssplit.
          red; intros.
          red in H4; destruct (idx_dec pidx (obj_idx obj)); subst; smred.
          eapply DLIntactBound_step_neq; eauto.
          apply parent_not_in_subtree; auto.
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
          red; intros; dest_in; disc_rule_conds.
          apply DLIntactBound_step_neq.
          apply parent_not_in_subtree; auto.
        * red.
          red; intros; exfalso.
          red in H24; destruct (idx_dec pidx (obj_idx obj)); subst; smred.
        * eapply DLOldPreserved_orqs_equiv.
          intros; smred.

      + (** case [RsDownDown-silent] *)
        red; intros _.
        repeat ssplit.
        * red; repeat ssplit; try (red; intros; dest_in).
        * red.
          red; intros; exfalso.
          red in H13; destruct (idx_dec pidx (obj_idx obj)); subst; smred.
        * eapply DLOldPreserved_orqs_equiv.
          intros; smred.

      + (** case [RsUpDown] *)
        red; intros; exfalso.
        pose proof (RqRsDownMatch_rs_not_nil H22).
        destruct rins as [|rin rins];
          [apply eq_sym, map_eq_nil in H28; auto|].
        inv H17.
        eapply RqRsDownMatch_rs_rq in H22; [|rewrite <-H28; left; reflexivity].
        destruct H22 as [cidx [down ?]]; dest.
        eapply H6; [|left; reflexivity].
        right; red; eauto.

      + (** case [RsUpUp] *)
        red; intros; exfalso.
        pose proof (RqRsDownMatch_rs_not_nil H7).
        destruct rins as [|rin rins];
          [apply eq_sym, map_eq_nil in H28; auto|].
        inv H17.
        eapply RqRsDownMatch_rs_rq in H7; [|rewrite <-H28; left; reflexivity].
        destruct H7 as [cidx [down ?]]; dest.
        eapply H10; [|left; reflexivity].
        right; red; eauto.

      + (** case [RsUpUp-silent] *)
        red; intros; exfalso.
        pose proof (RqRsDownMatch_rs_not_nil H5).
        destruct rins as [|rin rins];
          [apply eq_sym, map_eq_nil in H28; auto|].
        inv H17.
        eapply RqRsDownMatch_rs_rq in H5; [|rewrite <-H28; left; reflexivity].
        destruct H5 as [cidx [down ?]]; dest.
        eapply H6; [|left; reflexivity].
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
        * red; intros; split.
          { disc_RqRsDownMatch_rq; disc_rule_conds.
            constructor.
            { red; smred; split; [discriminate|reflexivity]. }
            { intros; smred; disc_rule_conds; solve_midx_false. }
          }
          { disc_RqRsDownMatch_rq; disc_rule_conds.
            red; intros; smred.
            intro Hx; rewrite Hx in *.
            disc_rule_conds; auto.
          }
        * red; intros; disc_RqRsDownMatch_rq; disc_rule_conds.
      + red.
        red; intros.
        red in H4; destruct (idx_dec pidx (obj_idx obj)); subst; smred.
        eapply DLIntactBound_step_neq; eauto.
        apply parent_not_in_subtree; auto.
      + eapply DLOldPreserved_new; mred.

  Qed.

  Lemma atomic_down_lock_time_ok:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      forall st1 st2,
        Reachable (steps step_m) sys st1 ->
        steps step_m sys st1 hst st2 ->
        DLTimeInv st1.(st_orqs) st2.(st_orqs) inits eouts.
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
    assert (MsgOutsInv dtr (oindsOf (RlblInt oidx ridx rins routs :: hst))
                       (st_orqs st1) (st_orqs st2)
                       (removeL (id_dec msg_dec) eouts rins ++ routs)) as Hmoinv2.
    { eapply atomic_msg_outs_ok; eauto.
      { econstructor; eauto. }
      { econstructor; eauto. }
    }

    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule.

    - (** case [ImmDown] *)
      disc_rule_conds.
      inv Hmoinv; [apply SubList_nil_inv in H4; discriminate|
                   |disc_rule_conds|].
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
        apply DLIntactAll_DLIntactBound.
        eapply H26; [|left; reflexivity].
        red; eauto.
      + red; repeat ssplit; try assumption.
      + assumption.

    - (** case [ImmUp] *)
      disc_rule_conds.
      inv Hmoinv; [apply SubList_nil_inv in H4; discriminate|
                   disc_rule_conds; solve_midx_false|disc_rule_conds|].
      apply SubList_singleton_In in H4.

      replace (orqs +[obj_idx obj <- norq]) with orqs by meq.
      red; intros.
      specialize (IHAtomic H21); dest.
      red in H25, H27; dest.
      repeat ssplit.
      + apply DLOutsInv_app; [apply DLOutsInv_removeOnce|].
        * red; repeat ssplit; try assumption.
        * red; repeat ssplit; try (exfalso_wrong_msg_lock; fail).
          red; intros; dest_in; disc_rule_conds.
          eapply H30; eauto.
          red; auto.
      + red; repeat ssplit; try assumption.
      + assumption.

    - (** case [RqFwd] *)
      disc_rule_conds.
      + (** case [RqUpUp] *)
        inv Hmoinv; [apply SubList_nil_inv in H4; discriminate|
                     |disc_rule_conds|].
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
          eapply DLIntactAll_trans.
          { eapply H33; [|left; reflexivity]; red; eauto. }
          { red; intros; red; smred. }

        * red.
          red; intros.
          destruct (idx_dec pidx (obj_idx obj)); subst; smred.
          { exfalso.
            eapply DownLockedNew_not_DownLockIntact; [eassumption|].
            eapply steps_not_in_history_down_lock_intact
              with (oidx:= obj_idx obj) in H10.
            { eapply DownLockIntact_trans; [eassumption|].
              red; smred.
            }
            { intro Hx; apply H29 in Hx.
              eapply parent_not_in_subtree
                with (dtr:= dtr) (oidx:= oidx); eauto.
            }
          }
          { eapply DownLockIntact_DownLockedNew_2
              with (orqs3:= orqs) in H39; [|red; smred].
            eapply DLIntactBound_trans; eauto.
            eapply DLIntactBound_refl.
            intros; red; smred.
          }

        * eapply DLOldPreserved_orqs_step; [eassumption|].
          intros; smred.

      + (** case [RqUpDown] *)
        inv Hmoinv; [apply SubList_nil_inv in H4; discriminate|
                     |disc_rule_conds|].
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
        * red; repeat ssplit;
            try (red; intros; exfalso;
                 disc_RqRsDownMatch_rq; disc_rule_conds; solve_midx_false;
                 fail).
          red; intros; split.
          { disc_RqRsDownMatch_rq; disc_rule_conds.
            constructor.
            { eapply DownLockIntact_DownLockedNew_1 with (orqs2:= orqs).
              { eapply H32; [|left; reflexivity]; red; eauto. }
              { red; smred; split; [discriminate|reflexivity]. }
            }
            { intros; smred.
              rewrite H42 in *; solve_midx_false.
            }
          }
          { disc_RqRsDownMatch_rq; disc_rule_conds.
            red; intros; smred.
            intro Hx; rewrite Hx in *.
            disc_rule_conds; auto.
          }

        * red; repeat ssplit.
          red; intros.
          destruct (idx_dec pidx (obj_idx obj)); subst; smred.
          { eapply DLIntactBound_trans with (orqs2:= orqs); eauto.
            { apply DLIntactAll_DLIntactBound.
              eapply H32; [|left; reflexivity]; red; eauto.
            }
            { eapply DLIntactBound_step_neq; eauto.
              eapply parent_not_in_subtree; eauto.
            }
          }
          { eapply DownLockIntact_DownLockedNew_2
              with (orqs3:= orqs) in H39; [|red; smred].
            exfalso; eapply DownLockedNew_not_DownLockIntact; [eassumption|].
            eapply H32; [|left; reflexivity]; red; eauto.
          }

        * eapply DLOldPreserved_trans; [eassumption|].
          eapply DLOldPreserved_new; smred.

      + (** case [RqDownDown] *)
        inv Hmoinv; [apply SubList_nil_inv in H4; discriminate|
                     disc_rule_conds; solve_midx_false|disc_rule_conds|].
        apply SubList_singleton_In in H4; subst.

        pose proof H14.
        rewrite Forall_forall in H28; specialize (H28 _ H4); destruct H28 as [roidx ?].
        destruct H28; [|red in H28; red; dest; disc_rule_conds].
        red in H28; dest.
        disc_rule_conds.

        red; intros.
        specialize (IHAtomic H32); dest.
        red in H33, H34; dest.
        repeat ssplit.

        * apply DLOutsInv_app.
          { apply DLOutsInv_removeOnce.
            pose proof H14.
            eapply rqDown_rsUp_inv_msg in H41; rewrite Forall_forall in H41.
            red; repeat ssplit.
            { red; intros; exfalso.
              specialize (H41 _ H44); destruct H41 as [rroidx ?].
              destruct H41; disc_rule_conds; solve_midx_false.
            }
            { red; intros; exfalso.
              specialize (H41 _ H44); destruct H41 as [rroidx ?].
              destruct H41; disc_rule_conds; solve_midx_false.
            }
            { red; intros.
              specialize (H38 _ _ _ H43 H44 H45); dest.
              split.
              { destruct (in_dec idx_dec pidx (subtreeIndsOf dtr (obj_idx obj))).
                { exfalso; inv H38.
                  eapply DownLockedNew_in_history in H10; [|eassumption].
                  eapply DisjList_In_1; [apply H29| |]; eauto.
                }
                { eapply DLNewRec_orqs_step_intact; try eassumption.
                  intro Hx; subst.
                  elim n; eapply rsEdgeUpFrom_subtreeIndsOf_self_in; eauto; congruence.
                }
              }
              { destruct (idx_dec pidx (obj_idx obj)).
                { subst; exfalso.
                  inv H38; red in H47; smred.
                }
                { red; intros; smred; eapply H46; eauto. }
              }
            }
            { red; intros.
              specialize (H39 _ _ _ H43 H44 H45).
              destruct (in_dec idx_dec pidx (subtreeIndsOf dtr (obj_idx obj))).
              { exfalso; inv H39.
                eapply DownLockedNew_in_history in H10; [|eassumption].
                eapply DisjList_In_1; [apply H29| |]; eauto.
              }
              { eapply DLNewRec_orqs_step_intact; try eassumption.
                intro Hx; subst.
                elim n; eapply rsEdgeUpFrom_subtreeIndsOf_self_in; eauto; congruence.
              }
            }
          }
          { red; repeat ssplit;
              try (red; intros; exfalso;
                   disc_RqRsDownMatch_rq; disc_rule_conds; solve_midx_false;
                   fail).
            red; intros.
            disc_RqRsDownMatch_rq; disc_rule_conds.
            split.
            { constructor.
              { eapply DownLockIntact_DownLockedNew_1 with (orqs2:= orqs).
                { eapply steps_not_in_history_down_lock_intact in H10; [eassumption|].
                  destruct H14; [|exfalso; red in H14; dest; disc_rule_conds].
                  red in H14; dest; disc_rule_conds.
                  eapply DisjList_In_1; [eassumption|].
                  eapply parent_subtreeIndsOf_self_in; eauto.
                }
                { red; smred; split; [discriminate|reflexivity]. }
              }
              { intros; smred.
                eapply DLNewRec_orqs_step_intact.
                { eapply H38; eauto; red; auto. }
                { intro Hx; subst; apply parentIdxOf_not_eq in H51; auto. }
                { intro Hx; apply parent_not_in_subtree in H51; auto. }
              }
            }
            { red; intros; smred.
              intro Hx; rewrite Hx in *; inv H42.
              solve_midx_false.
            }
          }

        * (** The trickiest case .. *)
          red.
          red; intros.
          destruct (idx_dec pidx (obj_idx obj)); subst; smred;
            [rewrite H42 in *; solve_midx_false|].
          eapply DownLockIntact_DownLockedNew_2 in H41; [|red; smred].
          destruct (in_dec idx_dec (obj_idx obj) (subtreeIndsOf dtr cidx)).
          { exfalso.
            pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H5) as Hed.
            destruct Hed as [rqUp [rsUp [rpidx ?]]]; dest.
            disc_rule_conds.

            assert (RqDownMsgTo dtr (obj_idx obj) (rqFrom, rqfm)) by (red; auto).
            specialize (H38 _ _ _ H49 H50 H4); dest.

            assert (~ In rpidx (subtreeIndsOf dtr cidx)).
            { intro Hx.
              move H34 at bottom.
              specialize (H34 _ _ _ H41 H43 H44 _ H45 H46 _ Hx).
              inv H38; eapply DownLockedNew_not_DownLockIntact; eassumption.
            }
            eapply inside_child_outside_parent_case in H52; eauto; subst.
            disc_rule_conds.
            specialize (H51 _ _ H43 H44); auto.
          }
          { eapply DLIntactBound_trans with (orqs2:= orqs); eauto.
            apply DLIntactBound_step_neq; assumption.
          }

        * eapply DLOldPreserved_trans; [eassumption|].
          eapply DLOldPreserved_new; smred.

    - (** case [RsBack] *)
      good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + (** case [RsDownDown] *)
        inv Hmoinv; [apply SubList_nil_inv in H4; discriminate|disc_rule_conds| |].
        2: {
          simpl in *.
          apply rqDown_rsUp_inv_msg in H29; rewrite Forall_forall in H29.
          apply SubList_singleton_In in H4.
          specialize (H29 _ H4); destruct H29 as [oidx ?].
          destruct H29; disc_rule_conds; solve_midx_false.
        }

        apply SubList_singleton in H4; subst.
        rewrite removeOnce_nil; simpl.
        disc_rule_conds.
        red; intros.
        specialize (IHAtomic H28); dest.
        red in H34, H35; dest.
        repeat ssplit.

        * red; repeat ssplit; try (exfalso_wrong_msg_lock; fail).
          red; intros; dest_in; disc_rule_conds.
          eapply DLIntactBound_trans with (orqs2:= orqs).
          { eapply DLIntactBound_child; [|eassumption].
            eapply H37; [|left; reflexivity]; red; auto.
          }
          { apply DLIntactBound_step_neq.
            apply parent_not_in_subtree; auto.
          }

        * red.
          red; intros.
          destruct (idx_dec pidx (obj_idx obj)); subst; smred.
          eapply DownLockIntact_DownLockedNew_2
            with (orqs3:= orqs) in H40; [|red; smred].
          eapply DLIntactBound_trans; eauto.
          eapply DLIntactBound_refl.
          intros; red; smred.

        * eapply DLOldPreserved_orqs_step; [eassumption|].
          intros; smred.

      + (** case [RsDownDown-silent] *)
        inv Hmoinv; [apply SubList_nil_inv in H4; discriminate|disc_rule_conds| |].
        2: {
          apply rqDown_rsUp_inv_msg in H25; rewrite Forall_forall in H25.
          apply SubList_singleton_In in H4.
          specialize (H25 _ H4); destruct H25 as [oidx ?].
          destruct H25; disc_rule_conds; solve_midx_false.
        }

        apply SubList_singleton in H4; subst.
        rewrite removeOnce_nil; simpl.
        disc_rule_conds.
        red; intros.
        specialize (IHAtomic H17); dest.
        red in H30, H31; dest.
        repeat ssplit.

        * red; repeat ssplit; try (red; intros; dest_in).
        * red.
          red; intros.
          destruct (idx_dec pidx (obj_idx obj)); subst; smred.
          eapply DownLockIntact_DownLockedNew_2
            with (orqs3:= orqs) in H37; [|red; smred].
          eapply DLIntactBound_trans; eauto.
          eapply DLIntactBound_refl.
          intros; red; smred.
        * eapply DLOldPreserved_orqs_step; [eassumption|].
          intros; smred.

      + (** case [RsUpDown] *)
        inv Hmoinv2.
        1: { destruct (removeL _ _ _); discriminate. }
        1: {
          exfalso.
          assert (rqUp = (rsbTo0, rsm)); subst.
          { destruct (removeL _ eouts rins); [inv H9; reflexivity|].
            destruct l; discriminate.
          }
          disc_rule_conds.
        }
        2: {
          exfalso.
          apply rqDown_rsUp_inv_msg, Forall_app_inv in H28; dest.
          inv H33; destruct H36 as [oidx ?].
          destruct H33; disc_rule_conds; solve_midx_false.
        }
        destruct (removeL _ eouts rins); [|destruct l; discriminate].
        inv H9.

        disc_rule_conds.
        red; intros.
        specialize (IHAtomic H28); dest.
        red in H34, H35; dest.

        (* Below is used multiple times so prove it in advance. *)
        assert (DownLockedNew (st_orqs st1) orqs (obj_idx obj)) as Hdln.
        { pose proof H26.
          eapply RqRsDownMatch_rs_not_nil in H26.
          destruct rins as [|rin rins]; [exfalso; auto|].
          eapply RqRsDownMatch_rs_rq in H41; [|rewrite <-H32; left; reflexivity].
          destruct H41 as [cidx [down ?]]; dest.
          disc_rule_conds.

          assert (RsUpMsgFrom dtr cidx rin) by (red; eauto).
          assert (In rin eouts) by (apply H4; left; reflexivity).
          specialize (H40 _ _ _ H17 H42 H21).
          inv H40; assumption.
        }

        repeat ssplit.
        * red; repeat ssplit; try (exfalso_wrong_msg_lock; fail).
          red; intros; dest_in; disc_rule_conds.
          eapply DLIntactBound_trans with (orqs2:= orqs).
          { eapply H36; try eassumption.
            congruence.
          }
          { apply DLIntactBound_step_neq.
            apply parent_not_in_subtree; auto.
          }
        * red; apply DLNewBackUpLockedNew_orqs_step_remove; try assumption; mred.
        * apply DLOldPreserved_remove; try assumption; mred.

      + (** case [RsUpUp] *)
        inv Hmoinv2.
        1: { destruct (removeL _ _ _); discriminate. }
        1: {
          exfalso.
          destruct (removeL _ eouts rins); [|destruct l; discriminate].
          inv H14; disc_rule_conds.
        }
        1: {
          exfalso.
          destruct (removeL _ eouts rins); [|destruct l; discriminate].
          inv H14; disc_rule_conds; solve_midx_false.
        }
        clear H26 H28. (* Clear useless invariants, except [RqDownRsUpDisj]. *)
        apply rqDown_rsUp_inv_msg in H25.
        apply Forall_app_inv in H25; dest; clear H26.
        rewrite Forall_forall in H25.
        rename H21 into Hrrd, H25 into Hrri.

        red; intros.
        specialize (IHAtomic H21); dest.
        red in H25; dest.

        (* Below is used multiple times so prove it in advance. *)
        assert (exists cidx rsUp,
                   In rsUp rins /\
                   RsUpMsgFrom dtr cidx rsUp /\
                   parentIdxOf dtr cidx = Some (obj_idx obj) /\
                   DLNewRec (st_orqs st1) orqs (obj_idx obj)) as Hdln.
        { pose proof H12.
          eapply RqRsDownMatch_rs_not_nil in H34.
          destruct rins as [|rin rins]; [exfalso; auto|].
          eapply RqRsDownMatch_rs_rq in H12; [|rewrite <-H32; left; reflexivity].
          destruct H12 as [cidx [down ?]]; dest.
          disc_rule_conds.
          assert (RsUpMsgFrom dtr cidx rin) by (red; eauto).
          assert (In rin eouts) by (apply H4; left; reflexivity).
          specialize (H33 _ _ _ H17 H35 H39).
          exists cidx, rin; repeat ssplit; try assumption.
          left; reflexivity.
        }
        destruct Hdln as [cidx [rsUp ?]]; dest.

        repeat ssplit.
        * apply DLOutsInv_app.
          { red; repeat ssplit.
            { red; intros; exfalso.
              specialize (Hrri _ H39); destruct Hrri as [roidx ?].
              destruct H40; disc_rule_conds; solve_midx_false.
            }
            { red; intros; exfalso.
              specialize (Hrri _ H39); destruct Hrri as [roidx ?].
              destruct H40; disc_rule_conds; solve_midx_false.
            }
            { red; intros.
              destruct (in_dec idx_dec pidx (subtreeIndsOf dtr (obj_idx obj))).
              { exfalso.
                eapply inside_child_in in i; eauto.
                eapply rqDownRsUpDisj_in_spec; try eapply i; eauto.
                { apply in_or_app; left; eassumption. }
                { apply in_or_app; right; left; reflexivity. }
                { intro Hx; subst; disc_rule_conds. }
                { left; assumption. }
                { right; red; auto. }
              }
              { assert (obj_idx obj <> pidx).
                { intro Hx; subst; elim n.
                  eapply parent_subtreeIndsOf_self_in; eauto.
                }
                split.
                { apply DLNewRec_orqs_step_intact; try assumption.
                  eapply H31; eauto; eapply removeL_In_2; eauto.
                }
                { red; smred.
                  eapply H31; eauto; eapply removeL_In_2; eauto.
                }
              }
            }
            { red; intros.
              destruct (in_dec idx_dec pidx (subtreeIndsOf dtr (obj_idx obj))).
              { exfalso.
                assert (In oidx (subtreeIndsOf dtr (obj_idx obj)))
                  by (eapply inside_child_in; eauto).
                eapply rqDownRsUpDisj_in_spec; try eapply H41; eauto.
                { apply in_or_app; left; eassumption. }
                { apply in_or_app; right; left; reflexivity. }
                { intro Hx; subst; disc_rule_conds.
                  eapply parent_not_in_subtree with (dtr:= dtr); eauto.
                }
                { right; assumption. }
                { right; red; auto. }
              }
              { assert (obj_idx obj <> pidx).
                { intro Hx; subst; elim n.
                  eapply parent_subtreeIndsOf_self_in; eauto.
                }
                apply DLNewRec_orqs_step_intact; try assumption.
                eapply H33; eauto; eapply removeL_In_2; eauto.
              }
            }
          }

          { red; repeat ssplit; try (exfalso_wrong_msg_lock; fail).
            red; intros; dest_in; disc_rule_conds.
            eapply DLNewRec_orqs_step_intact.
            { inv H37; eapply H42; eauto.
              congruence.
            }
            { intro Hx; subst.
              apply parentIdxOf_not_eq in H39; auto.
            }
            { apply parent_not_in_subtree; auto. }
          }

        * inv H37; red; apply DLNewBackUpLockedNew_orqs_step_remove; try assumption; mred.
        * inv H37; apply DLOldPreserved_remove; try assumption; mred.

      + (** case [RsUpUp-silent] *)
        rewrite app_nil_r in *.
        red; intros.
        specialize (IHAtomic H9); dest.

        (* Below is used multiple times so prove it in advance. *)
        assert (exists cidx rsUp,
                   In rsUp rins /\
                   RsUpMsgFrom dtr cidx rsUp /\
                   parentIdxOf dtr cidx = Some (obj_idx obj) /\
                   DLNewRec (st_orqs st1) orqs (obj_idx obj)) as Hdnr.
        { pose proof H7.
          eapply RqRsDownMatch_rs_not_nil in H25.
          destruct rins as [|rin rins]; [exfalso; auto|].
          eapply RqRsDownMatch_rs_rq in H7; [|rewrite <-H32; left; reflexivity].
          destruct H7 as [cidx [down ?]]; dest.
          disc_rule_conds.
          assert (RsUpMsgFrom dtr cidx rin) by (red; eauto).
          assert (In rin eouts) by (apply H4; left; reflexivity).
          red in H12; dest.
          specialize (H39 _ _ _ H17 H26 H21).
          exists cidx, rin; repeat ssplit; try assumption.
          left; reflexivity.
        }
        destruct Hdnr as [cidx [rsUp ?]]; dest.

        assert (DownLockedNew (st_orqs st1) orqs (obj_idx obj))
          as Hdln by (inv H30; assumption).

        inv Hmoinv.
        1: { exfalso; apply SubList_nil_inv in H4; auto. }
        1: { exfalso.
             apply SubList_singleton_NoDup in H4; [|apply IndexSupport.idsOf_NoDup; apply H18].
             destruct H4; [auto|subst].
             dest_in; inv H21.
             destruct H31; rewrite H4 in H37; discriminate.
        }
        1: { exfalso.
             apply SubList_singleton_NoDup in H4; [|apply IndexSupport.idsOf_NoDup; apply H18].
             destruct H4; [auto|subst].
             dest_in; inv H21.
             destruct H26, H31.
             solve_midx_false.
        }
        pose proof H33 as Hrrd.
        apply rqDown_rsUp_inv_msg in H33.
        rewrite Forall_forall in H33; rename H33 into Hrri.

        repeat ssplit.
        * red; repeat ssplit.
          { red; intros; exfalso.
            apply removeL_In_2 in H36.
            specialize (Hrri _ H36); destruct Hrri as [roidx ?].
            destruct H37; disc_rule_conds; solve_midx_false.
          }
          { red; intros; exfalso.
            apply removeL_In_2 in H36.
            specialize (Hrri _ H36); destruct Hrri as [roidx ?].
            destruct H37; disc_rule_conds; solve_midx_false.
          }

          { red; intros.
            destruct (in_dec idx_dec pidx (subtreeIndsOf dtr (obj_idx obj))).
            { exfalso.
              assert (In (obj_idx obj) (oindsOf hst)) as Hoin
                  by (eapply DownLockedNew_in_history; eauto).
              eapply rsUp_no_other_messages_in in H7; try eassumption;
                [|apply H18| |right; assumption|apply Forall_forall; assumption].
              2: { apply H34; [assumption| |red; mred].
                   intro Hx.
                   apply removeL_In_2 in H37.
                   eapply rqDown_rsUp_inv_rqDown in Hrrd; eauto.
                   red in Hrrd; dest.
                   red in H40.
                   specialize (H40 _ Hoin Hx).
                   elim H40.
                   eapply inside_child_in; [apply Hrrs|eassumption..].
              }
              rewrite Forall_forall in H7.
              specialize (H7 _ H37).
              specialize (H7 _ (or_introl _ H33)).
              elim H7.
              eapply inside_child_in; [apply Hrrs|eassumption..].
            }
            { red in H12; dest.
              assert (obj_idx obj <> pidx).
              { intro Hx; subst; elim n.
                eapply parent_subtreeIndsOf_self_in; eauto.
              }
              split.
              { apply DLNewRec_orqs_step_intact; try assumption.
                eapply H39; eauto; eapply removeL_In_2; eauto.
              }
              { red; smred.
                eapply H39; eauto; eapply removeL_In_2; eauto.
              }
            }
          }

          { red; intros.
            destruct (in_dec idx_dec pidx (subtreeIndsOf dtr (obj_idx obj))).
            { exfalso.
              assert (In (obj_idx obj) (oindsOf hst)) as Hoin
                  by (eapply DownLockedNew_in_history; eauto).
              eapply rsUp_no_other_messages_in in H7; try eassumption;
                [|apply H18| |right; assumption|apply Forall_forall; assumption].
              2: { apply H34; [assumption| |red; mred].
                   intro Hx.
                   apply removeL_In_2 in H37.
                   eapply rqDown_rsUp_inv_rsUp in Hrrd; eauto.
                   red in Hrrd; dest.
                   red in H40.
                   specialize (H40 _ Hoin Hx).
                   elim H40.
                   eapply inside_child_in; [apply Hrrs|eassumption..].
              }
              rewrite Forall_forall in H7.
              specialize (H7 _ H37).
              specialize (H7 _ (or_intror _ H33)).
              elim H7.
              eapply inside_child_in; [apply Hrrs|eassumption..].
            }
            { red in H12; dest.
              assert (obj_idx obj <> pidx).
              { intro Hx; subst; elim n.
                eapply parent_subtreeIndsOf_self_in; eauto.
              }
              apply DLNewRec_orqs_step_intact; try assumption.
              eapply H40; eauto; eapply removeL_In_2; eauto.
            }
          }

        * apply DLNewBackUpLockedNew_orqs_step_remove; try assumption; mred.
        * apply DLOldPreserved_remove; try assumption; mred.

    - (** case [RsDownRqDown] *)
      good_footprint_get (obj_idx obj).
      disc_rule_conds.
      inv Hmoinv; [apply SubList_nil_inv in H4; discriminate|disc_rule_conds| |].
      2: {
        simpl in *.
        apply rqDown_rsUp_inv_msg in H27; rewrite Forall_forall in H27.
        apply SubList_singleton_In in H4.
        specialize (H27 _ H4); destruct H27 as [oidx ?].
        destruct H27; disc_rule_conds; solve_midx_false.
      }

      apply SubList_singleton in H4; subst.
      rewrite removeOnce_nil in *; simpl.
      disc_rule_conds.
      red; intros.
      specialize (IHAtomic H26); dest.
      red in H26, H33; dest.
      repeat ssplit.

      + red; repeat ssplit;
          try (red; intros; exfalso;
               disc_RqRsDownMatch_rq; disc_rule_conds; solve_midx_false;
               fail).
        red; intros.
        disc_RqRsDownMatch_rq; disc_rule_conds.
        split.
        * constructor.
          { eapply DownLockIntact_DownLockedNew_1 with (orqs2:= orqs).
            { eapply H34; [|left; reflexivity|].
              { red; eauto. }
              { eapply parent_subtreeIndsOf_self_in; eauto. }
            }
            { red; smred; split; [discriminate|reflexivity]. }
          }
          { intros; smred; disc_rule_conds; solve_midx_false. }
        * red; intros; smred.
          intro Hx; rewrite Hx in *.
          disc_rule_conds; auto.

      + (** Also quite tricky *)
        red.
        red; intros.
        destruct (idx_dec pidx (obj_idx obj)); subst; smred.
        * disc_rule_conds.
          eapply DLIntactBound_trans with (orqs2:= orqs); eauto.
          { eapply DLIntactBound_child; [|eassumption].
            eapply H34; [|left; reflexivity].
            red; auto.
          }
          { apply DLIntactBound_step_neq.
            apply parent_not_in_subtree; auto.
          }
        * eapply DownLockIntact_DownLockedNew_2
            with (orqs3:= orqs) in H41; [|red; smred].
          destruct (in_dec idx_dec (obj_idx obj) (subtreeIndsOf dtr cidx)).
          { exfalso.
            eapply DownLockedNew_in_history in H10; [|eassumption].
            assert (~ In pidx (subtreeIndsOf dtr (obj_idx obj))).
            { intro Hx.
              eapply subtreeIndsOf_child_SubList in i; eauto.
              elim n; eapply subtreeIndsOf_In_each_other_eq
                        with (dtr:= dtr); eauto.
            }
            specialize (H33 _ H10 H47).
            apply DownLockedNew_DownLocked in H41.
            destruct H41 as [rrqid ?].
            red in H33, H41; smred.
          }
          { eapply DLIntactBound_trans with (orqs2:= orqs); eauto.
            apply DLIntactBound_step_neq; assumption.
          }

      + eapply DLOldPreserved_trans; [eassumption|].
        eapply DLOldPreserved_new; smred.

  Qed.

End RqRsInvLockEx.

Section Corollaries.
  Context `{dv: DecValue} `{oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System).
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (oinvs: IdxT -> ObjInv)
             (Hrrs: RqRsSys dtr sys oinvs).

  Lemma extAtomic_DLTimeInits:
    forall inits trs eouts,
      ExtAtomic sys inits trs eouts ->
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
          ExtAtomic sys inits trs eouts ->
          forall cidx rsUp pidx,
            RsUpMsgFrom dtr cidx rsUp ->
            parentIdxOf dtr cidx = Some pidx ->
            In rsUp eouts ->
            DownLockedNew st1.(st_orqs) st2.(st_orqs) pidx.
  Proof.
    intros.
    pose proof (extAtomic_DLTimeInits H1).
    inv H1.
    eapply atomic_down_lock_time_ok in H7; eauto.
    specialize (H7 H5); dest.
    red in H1; dest.
    specialize (H11 _ _ _ H2 H3 H4).
    inv H11; assumption.
  Qed.

  Corollary extAtomic_rsUp_down_lock_preserved:
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall trs st2,
        steps step_m sys st1 trs st2 ->
        forall inits eouts,
          ExtAtomic sys inits trs eouts ->
          forall oidx rqid,
            DownLocked st1.(st_orqs) oidx rqid ->
            DownLocked st2.(st_orqs) oidx rqid.
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
        ExtAtomic sys inits1 trs1 eouts1 ->
        forall trss inits2 trs2 eouts2 st2,
          steps step_m sys st1 (trs2 ++ List.concat trss ++ trs1) st2 ->
          ExtAtomic sys inits2 trs2 eouts2 ->
          Forall AtomicEx trss ->
          Forall (Transactional sys) trss ->
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
    assert (DownLocked (st_orqs sti2) pidx rqid).
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
        Forall AtomicEx trss ->
        Forall (Transactional sys) trss ->
        forall n1 inits1 trs1 eouts1 n2 inits2 trs2 eouts2,
          n1 > n2 ->
          nth_error trss n1 = Some trs1 ->
          nth_error trss n2 = Some trs2 ->
          ExtAtomic sys inits1 trs1 eouts1 ->
          ExtAtomic sys inits2 trs2 eouts2 ->
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
      rewrite nth_error_app2 in H4; [|lia].
      apply nth_error_split in H4.
      destruct H4 as [ntrss1 [ptrss ?]]; dest; subst.
      destruct ntrss1; [simpl in *; lia|].
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
        Forall AtomicEx trss ->
        Forall (Transactional sys) trss ->
        forall n1 inits1 trs1 eouts1 n2 inits2 trs2 eouts2,
          n1 <> n2 ->
          nth_error trss n1 = Some trs1 ->
          nth_error trss n2 = Some trs2 ->
          ExtAtomic sys inits1 trs1 eouts1 ->
          ExtAtomic sys inits2 trs2 eouts2 ->
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
