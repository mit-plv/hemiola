Require Import PeanoNat Compare_dec Lia List.
Require Import Common FMap IndexSupport.
Require Import Syntax Semantics SemFacts StepM Invariant Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvMsg RqRsInvLock RqRsInvSep.
Require Import RqUpRed.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section Coverage.
  Context `{dv: DecValue} `{oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System).
  Hypotheses (Hiorqs: GoodORqsInit (initsOf sys))
             (oinvs: IdxT -> ObjInv)
             (Hrrs: RqRsSys dtr sys oinvs).

  Definition RqUpMsgFrom (oidx: IdxT) (idm: Id Msg) :=
    msg_type (valOf idm) = MRq /\
    rqEdgeUpFrom dtr oidx = Some (idOf idm).

  Definition RsDownMsgTo (oidx: IdxT) (idm: Id Msg) :=
    msg_type (valOf idm) = MRs /\
    edgeDownTo dtr oidx = Some (idOf idm).

  Definition RqDownMsgTo (oidx: IdxT) (idm: Id Msg) :=
    msg_type (valOf idm) = MRq /\
    edgeDownTo dtr oidx = Some (idOf idm).

  Definition RsUpMsgFrom (oidx: IdxT) (idm: Id Msg) :=
    msg_type (valOf idm) = MRs /\
    rsEdgeUpFrom dtr oidx = Some (idOf idm).

  Ltac disc_msg_case :=
    match goal with
    | [H: RqUpMsgFrom _ _ |- _] => destruct H
    | [H: RsDownMsgTo _ _ |- _] => destruct H
    | [H: RqDownMsgTo _ _ |- _] => destruct H
    | [H: RsUpMsgFrom _ _ |- _] => destruct H
    end.

  Section OnAtomic.
    Variables (oinds: list IdxT) (orqs1 orqs2: ORqs Msg).

    (** Invariants about history coverage with a tree *)

    Definition IndsInTree (ridx: IdxT) :=
      SubList oinds (subtreeIndsOf dtr ridx).

    Definition IndsDisjTree (ridx: IdxT) :=
      DisjList oinds (subtreeIndsOf dtr ridx).

    (** Invariants about uplocks *)

    Definition UpLocked (oidx: IdxT) :=
      orqs2@[oidx] >>=[False] (fun orq2 => orq2@[upRq] <> None).

    Definition UpLockedNew (oidx: IdxT) :=
      orqs2@[oidx] >>=[False]
           (fun orq2 =>
              orq2@[upRq] <> None /\
              orqs1@[oidx] >>=[True] (fun orq1 => orq1@[upRq] = None)).

    Definition UpLockedTotal :=
      forall oidx, In oidx oinds -> UpLockedNew oidx.

    Definition UpLockCoverInv (tidx: IdxT) :=
      forall oidx,
        In oidx (subtreeIndsOf dtr tidx) ->
        In oidx oinds ->
        forall orq2 rqiu,
          orqs2@[oidx] = Some orq2 ->
          orq2@[upRq] = Some rqiu ->
          forall cidx down,
            parentIdxOf dtr cidx = Some oidx ->
            edgeDownTo dtr cidx = Some down ->
            rqiu.(rqi_midx_rsb) <> Some down ->
            IndsDisjTree cidx.

    Definition UpLockedBound (tidx: IdxT) :=
      forall oidx,
        In oidx oinds ->
        UpLockedNew oidx ->
        In oidx (subtreeIndsOf dtr tidx).

    Definition OutsideUpLocked (oidx: IdxT) :=
      forall uidx,
        In uidx oinds ->
        UpLockedNew uidx ->
        ~ In oidx (subtreeIndsOf dtr uidx).

    Definition DisjExceptUpLocked (tidx: IdxT) :=
      forall oidx,
        In oidx oinds ->
        ~ UpLockedNew oidx ->
        ~ In oidx (subtreeIndsOf dtr tidx).

    (** Invariants about downlocks *)

    Definition NoDownLock (oidx: IdxT) :=
      orqs2@[oidx] >>=[True] (fun orq => orq@[downRq] = None).

    Definition NoDownLockOutside (roidx: IdxT) :=
      forall oidx,
        In oidx oinds ->
        ~ In oidx (subtreeIndsOf dtr roidx) ->
        NoDownLock oidx.

    Definition DownLocked (oidx: IdxT) (rqid: RqInfo Msg) :=
      orqs2@[oidx] >>=[False]
           (fun orq2 => orq2@[downRq] = Some rqid).

    Definition DownLockCoverInv (oidx: IdxT) (rqid: RqInfo Msg) :=
      forall cidx rsUp down,
        parentIdxOf dtr cidx = Some oidx ->
        rsEdgeUpFrom dtr cidx = Some rsUp ->
        edgeDownTo dtr cidx = Some down ->
        ~ In rsUp (map fst rqid.(rqi_rss)) ->
        rqid.(rqi_midx_rsb) <> Some down ->
        IndsDisjTree cidx.

    Definition DownLocksCoverInv :=
      forall oidx rqid,
        In oidx oinds ->
        ~ UpLockedNew oidx ->
        DownLocked oidx rqid ->
        DownLockCoverInv oidx rqid.

    Definition NoLocks2 (oinds2: list IdxT) :=
      forall oidx,
        In oidx oinds ->
        In oidx oinds2 ->
        ~ UpLockedNew oidx /\ NoDownLock oidx.

    (** Invariants for output messages *)

    Definition RqDownMsgOutInv (oidx: IdxT) (rqDown: Id Msg) :=
      RqDownMsgTo oidx rqDown /\
      IndsDisjTree oidx /\
      OutsideUpLocked oidx.

    Definition RsUpMsgOutInv (oidx: IdxT) (rsUp: Id Msg) :=
      RsUpMsgFrom oidx rsUp /\
      NoLocks2 (subtreeIndsOf dtr oidx) /\
      OutsideUpLocked oidx.

    Definition RqDownRsUpIdx (oidx: IdxT) (eout: Id Msg) :=
      RqDownMsgTo oidx eout \/ RsUpMsgFrom oidx eout.

    Definition RqDownRsUpDisj (eouts: list (Id Msg)) :=
      forall n1 oidx1 eout1 n2 oidx2 eout2,
        n1 <> n2 ->
        nth_error eouts n1 = Some eout1 ->
        RqDownRsUpIdx oidx1 eout1 ->
        nth_error eouts n2 = Some eout2 ->
        RqDownRsUpIdx oidx2 eout2 ->
        ~ In oidx1 (subtreeIndsOf dtr oidx2).

    (** Invariants for the downlock root *)

    (* The root of downlocks is the one that also has a downlock but
     * the return index ([rqi_midx_rsb]) is either None or Some of a child *)
    Definition DownLockRoot (roidx: IdxT) (rrqid: RqInfo Msg) (orcidx: option IdxT) :=
      In roidx oinds /\
      ~ UpLockedNew roidx /\ DownLocked roidx rrqid /\
      match orcidx with
      | Some rcidx => parentIdxOf dtr rcidx = Some roidx /\
                      edgeDownTo dtr rcidx = rrqid.(rqi_midx_rsb)
      | None => rrqid.(rqi_midx_rsb) = None
      end.

    Definition RqDownInRoot (roidx: IdxT) (orcidx: option IdxT) (eout: Id Msg) :=
      forall oidx pidx,
        RqDownMsgTo oidx eout ->
        parentIdxOf dtr oidx = Some pidx ->
        In pidx (subtreeIndsOf dtr roidx) /\
        orcidx >>=[True] (fun rcidx => ~ In oidx (subtreeIndsOf dtr rcidx)).

    Definition RsUpInRoot (roidx: IdxT) (orcidx: option IdxT) (eout: Id Msg) :=
      forall oidx pidx,
        RsUpMsgFrom oidx eout ->
        parentIdxOf dtr oidx = Some pidx ->
        In pidx (subtreeIndsOf dtr roidx) /\
        orcidx >>=[True] (fun rcidx => ~ In oidx (subtreeIndsOf dtr rcidx)).

    Definition OutInRoot (roidx: IdxT) (orcidx: option IdxT) (eout: Id Msg) :=
      RqDownInRoot roidx orcidx eout /\ RsUpInRoot roidx orcidx eout.

    Definition OutsInRoot (roidx: IdxT) (orcidx: option IdxT) (eouts: list (Id Msg)) :=
      Forall (OutInRoot roidx orcidx) eouts.

    Definition DownLockRootInv (roidx: IdxT) (orcidx: option IdxT) (eouts: list (Id Msg)) :=
      OutsInRoot roidx orcidx eouts /\
      match orcidx with
      | Some rcidx => DisjExceptUpLocked rcidx /\
                      UpLockCoverInv rcidx /\
                      UpLockedBound rcidx
      | None => True
      end /\
      NoDownLockOutside roidx.

    (** The final combined invariant for output messages *)

    Inductive MsgOutsInv: list (Id Msg) -> Prop :=
    | MsgOutsNil: MsgOutsInv nil
    | MsgOutsRqUp: (* Only one RqUp-output message *)
        forall oidx rqUp,
          RqUpMsgFrom oidx rqUp ->
          UpLockCoverInv oidx ->
          UpLockedBound oidx ->
          SubList oinds (subtreeIndsOf dtr oidx) ->
          UpLockedTotal ->
          MsgOutsInv [rqUp]
    | MsgOutsRsDown: (* Only one RsDown-output message *)
        forall oidx rsDown,
          RsDownMsgTo oidx rsDown ->
          DisjExceptUpLocked oidx ->
          UpLockCoverInv oidx ->
          UpLockedBound oidx ->
          NoDownLockOutside oidx ->
          MsgOutsInv [rsDown]
    | MsgOutsRqDownRsUp: (* RqDown or RsUp messages *)
        forall eouts,
          RqDownRsUpDisj eouts ->
          Forall (fun eout =>
                    exists oidx,
                      RqDownMsgOutInv oidx eout \/
                      RsUpMsgOutInv oidx eout) eouts ->
          DownLocksCoverInv ->
          (forall roidx rrqid orcidx,
              DownLockRoot roidx rrqid orcidx ->
              DownLockRootInv roidx orcidx eouts) ->
          MsgOutsInv eouts.

  End OnAtomic.

  (*! Facts *)

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_messages_in;
    try disc_msg_case.

  Ltac simpl_lock :=
    match goal with
    | [H: UpLockedNew _ _ _ |- _] =>
      unfold UpLockedNew in H; repeat (simpl in H; mred)
    | [H: ~ UpLockedNew _ _ _ |- _] =>
      unfold UpLockedNew in H; repeat (simpl in H; mred)
    | [H: DownLocked _ _ _ |- _] =>
      unfold DownLocked in H; repeat (simpl in H; mred)
    | [H: ~ DownLocked _ _ _ |- _] =>
      unfold DownLocked in H; repeat (simpl in H; mred)
    | [H: NoDownLock _ _ |- _] => red in H; repeat (simpl in H; mred)
    | [ |- UpLockedNew _ _ _] =>
      unfold UpLockedNew; repeat (simpl; mred)
    | [ |- ~ UpLockedNew _ _ _] =>
      unfold UpLockedNew; repeat (simpl; mred)
    | [ |- DownLocked _ _ _] =>
      unfold DownLocked; repeat (simpl; mred)
    | [ |- ~ DownLocked _ _ _] =>
      unfold DownLocked; repeat (simpl; mred)
    | [ |- NoDownLock _ _] => red; repeat (simpl; mred)
    end.
  Ltac simpl_locks := repeat simpl_lock.

  Lemma rqDownRsUpIdx_oidx_eq:
    forall oidx1 oidx2 eout,
      RqDownRsUpIdx oidx1 eout ->
      RqDownRsUpIdx oidx2 eout ->
      oidx1 = oidx2.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    destruct H2, H3; disc_rule_conds; solve_midx_false.
  Qed.

  Lemma rqDownRsUpDisj_cons:
    forall eouts,
      RqDownRsUpDisj eouts ->
      forall eout,
        (forall oidx,
            RqDownRsUpIdx oidx eout ->
            forall oidx2 eout2,
              In eout2 eouts ->
              RqDownRsUpIdx oidx2 eout2 ->
              ~ In oidx (subtreeIndsOf dtr oidx2) /\
              ~ In oidx2 (subtreeIndsOf dtr oidx)) ->
        RqDownRsUpDisj (eout :: eouts).
  Proof.
    intros.
    red; intros.
    destruct n1 as [|n1].
    - simpl in H2; inv H2.
      destruct n2 as [|n2]; [exfalso; auto|].
      simpl in H4.
      eapply (H0 _ H3); eauto.
      eapply nth_error_In; eauto.
    - destruct n2 as [|n2].
      + simpl in *; inv H4.
        eapply (H0 _ H5); eauto.
        eapply nth_error_In; eauto.
      + simpl in *.
        eapply H with (n1:= n1) (n2:= n2); eauto.
  Qed.

  Lemma rqDownRsUpDisj_cons_inv:
    forall eout eouts,
      RqDownRsUpDisj (eout :: eouts) ->
      (forall oidx,
          RqDownRsUpIdx oidx eout ->
          forall oidx2 eout2,
            In eout2 eouts ->
            RqDownRsUpIdx oidx2 eout2 ->
            ~ In oidx (subtreeIndsOf dtr oidx2) /\
            ~ In oidx2 (subtreeIndsOf dtr oidx)) /\
      RqDownRsUpDisj eouts.
  Proof.
    intros; split.
    - intros; split.
      + apply In_nth_error in H1.
        destruct H1 as [n2 ?].
        eapply H with (n1:= O) (n2:= S n2); eauto.
        reflexivity.
      + apply In_nth_error in H1.
        destruct H1 as [n2 ?].
        eapply H with (n1:= S n2) (n2:= O); eauto.
        reflexivity.
    - red; intros; eapply H with (n1:= S n1) (n2:= S n2); eauto.
  Qed.

  Lemma rqDownRsUpDisj_in_spec:
    forall eouts,
      RqDownRsUpDisj eouts ->
      forall oidx1 eout1 oidx2 eout2,
        In eout1 eouts -> In eout2 eouts -> eout1 <> eout2 ->
        RqDownRsUpIdx oidx1 eout1 ->
        RqDownRsUpIdx oidx2 eout2 ->
        ~ In oidx1 (subtreeIndsOf dtr oidx2).
  Proof.
    intros.
    apply In_nth_error in H0; destruct H0 as [n1 ?].
    apply In_nth_error in H1; destruct H1 as [n2 ?].
    eapply H with (n1:= n1) (n2:= n2); try eassumption.
    intro Hx; subst; congruence.
  Qed.

  Lemma rqDownRsUpDisj_app:
    forall eouts1 eouts2,
      RqDownRsUpDisj eouts1 ->
      RqDownRsUpDisj eouts2 ->
      (forall oidx1 eout1 oidx2 eout2,
          In eout1 eouts1 ->
          RqDownRsUpIdx oidx1 eout1 ->
          In eout2 eouts2 ->
          RqDownRsUpIdx oidx2 eout2 ->
          ~ In oidx1 (subtreeIndsOf dtr oidx2) /\
          ~ In oidx2 (subtreeIndsOf dtr oidx1)) ->
      RqDownRsUpDisj (eouts1 ++ eouts2).
  Proof.
    intros.
    red; intros.
    destruct (lt_dec n1 (length eouts1)).
    - rewrite nth_error_app1 in H3 by assumption.
      destruct (lt_dec n2 (length eouts1)).
      + rewrite nth_error_app1 in H5 by assumption.
        eapply H; eauto.
      + rewrite nth_error_app2 in H5 by lia.
        apply nth_error_In in H3.
        apply nth_error_In in H5.
        eapply H1 with (oidx1:= oidx1) (oidx2:= oidx2); eauto.
    - rewrite nth_error_app2 in H3 by lia.
      destruct (lt_dec n2 (length eouts1)).
      + rewrite nth_error_app1 in H5 by assumption.
        apply nth_error_In in H3.
        apply nth_error_In in H5.
        eapply H1 with (oidx1:= oidx2) (oidx2:= oidx1); eauto.
      + rewrite nth_error_app2 in H5 by lia.
        eapply H0 with (n1:= n1 - length eouts1) (n2:= n2 - length eouts1); eauto.
        lia.
  Qed.

  Lemma rqDownRsUpDisj_NoDup:
    forall eouts,
      Forall (fun eout =>
                exists oidx, RqDownRsUpIdx oidx eout) eouts ->
      RqDownRsUpDisj eouts -> NoDup (idsOf eouts).
  Proof.
    destruct Hrrs as [? [? ?]].
    induction eouts as [|eout eouts]; simpl; intros; [constructor|].
    apply rqDownRsUpDisj_cons_inv in H3; dest.
    inv H2; constructor; auto.
    destruct H7 as [oidx ?]; destruct H2.
    - intro Hx.
      apply in_map_iff in Hx.
      destruct Hx as [[midx msg] [? ?]]; simpl in *; subst.
      rewrite Forall_forall in H8.
      specialize (H8 _ H6).
      destruct H8 as [roidx ?].
      specialize (H3 _ (or_introl H2) _ _ H6 H5); dest.
      destruct H5.
      + disc_rule_conds; elim H3.
        apply edgeDownTo_subtreeIndsOf_self_in; [apply Hrrs|congruence].
      + disc_rule_conds; solve_midx_false.
    - intro Hx.
      apply in_map_iff in Hx.
      destruct Hx as [[midx msg] [? ?]]; simpl in *; subst.
      rewrite Forall_forall in H8.
      specialize (H8 _ H6).
      destruct H8 as [roidx ?].
      specialize (H3 _ (or_intror H2) _ _ H6 H5); dest.
      destruct H5.
      + disc_rule_conds; solve_midx_false.
      + disc_rule_conds; elim H3.
        apply rsEdgeUpFrom_subtreeIndsOf_self_in; [apply Hrrs|congruence].
  Qed.

  Lemma rqDownRsUpDisj_singleton:
    forall eout, RqDownRsUpDisj [eout].
  Proof.
    intros; red; intros.
    pose proof (nth_error_Some [eout] n1).
    pose proof (nth_error_Some [eout] n2).
    rewrite H0 in H4; rewrite H2 in H5; simpl in *.
    assert (Some eout1 <> None) by discriminate.
    assert (Some eout2 <> None) by discriminate.
    apply H4 in H6; apply H5 in H7.
    lia.
  Qed.

  Lemma rqDownRsUpDisj_removeOnce:
    forall eouts rmsg,
      RqDownRsUpDisj eouts ->
      RqDownRsUpDisj (removeOnce (id_dec msg_dec) rmsg eouts).
  Proof.
    induction eouts; simpl; intros; auto.
    apply rqDownRsUpDisj_cons_inv in H; dest.
    destruct (id_dec msg_dec rmsg a); subst; auto.
    apply rqDownRsUpDisj_cons; auto.
    intros.
    apply removeOnce_In_2 in H2.
    eapply H; eauto.
  Qed.

  Lemma rqDownRsUpDisj_removeL:
    forall rmsgs eouts,
      RqDownRsUpDisj eouts ->
      RqDownRsUpDisj (removeL (id_dec msg_dec) eouts rmsgs).
  Proof.
    induction rmsgs; simpl; intros; auto.
    apply IHrmsgs.
    apply rqDownRsUpDisj_removeOnce; auto.
  Qed.

  Lemma rqDownRsUpDisj_removeOnce_add_same:
    forall eouts,
      Forall (fun eout => exists oidx, RqDownRsUpIdx oidx eout) eouts ->
      RqDownRsUpDisj eouts ->
      forall rmsg amsg oidx,
        In rmsg eouts ->
        RqDownRsUpIdx oidx rmsg ->
        RqDownRsUpIdx oidx amsg ->
        RqDownRsUpDisj (removeOnce (id_dec msg_dec) rmsg eouts ++ [amsg]).
  Proof.
    intros.
    pose proof (rqDownRsUpDisj_NoDup H H0).
    apply rqDownRsUpDisj_app;
      [apply rqDownRsUpDisj_removeOnce; auto
      |apply rqDownRsUpDisj_singleton|].

    intros; dest_in.
    eapply removeOnce_In_NoDup in H5; [dest|apply idsOf_NoDup; assumption].
    split.
    - eapply rqDownRsUpIdx_oidx_eq in H3; [|eassumption]; subst.
      eapply rqDownRsUpDisj_in_spec with (eout1:= eout1) (eout2:= rmsg); eauto.
    - eapply rqDownRsUpIdx_oidx_eq in H3; [|eassumption]; subst.
      eapply rqDownRsUpDisj_in_spec with (eout1:= rmsg) (eout2:= eout1); eauto.
  Qed.

  Lemma rqDownRsUpDisj_down_children:
    forall oidx routs rss P,
      NoDup (idsOf routs) ->
      RqRsDownMatch dtr oidx (idsOf routs) rss P ->
      RqDownRsUpDisj routs.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    assert (Forall (fun rout =>
                      exists cidx,
                        parentIdxOf dtr cidx = Some oidx /\
                        edgeDownTo dtr cidx = Some (idOf rout)) routs).
    { red in H3; dest.
      clear -H2 H4 H5.
      generalize dependent rss.
      induction routs; simpl; intros; [constructor|].
      destruct rss; [discriminate|].
      inv H2; inv H4; inv H5.
      constructor; eauto.
      destruct H4 as [cidx ?]; dest; simpl in *.
      exists cidx; auto.
    }
    clear -H H2 H4.

    induction routs as [|rout routs]; simpl; intros;
      [red; intros; destruct n1; discriminate|].
    inv H2; inv H4.
    eapply rqDownRsUpDisj_cons; eauto.
    clear IHrouts.
    intros.
    destruct H2 as [ncidx [? ?]].
    rewrite Forall_forall in H6; specialize (H6 _ H1).
    destruct H6 as [cidx [? ?]].

    destruct H0; [|disc_rule_conds; solve_midx_false].
    destruct H4; [|disc_rule_conds; solve_midx_false].
    disc_rule_conds.

    split.
    - eapply subtreeIndsOf_other_child_not_in; [apply H|..]; try eassumption.
      intro Hx; subst.
      disc_rule_conds.
      destruct rout as [ridx rmsg], eout2 as [eidx emsg].
      simpl in *; subst.
      elim H3.
      apply in_map with (f:= idOf) in H1; assumption.
    - eapply subtreeIndsOf_other_child_not_in; [apply H|..]; try eassumption.
      intro Hx; subst.
      disc_rule_conds.
      destruct rout as [ridx rmsg], eout2 as [eidx emsg].
      simpl in *; subst.
      elim H3.
      apply in_map with (f:= idOf) in H1; assumption.
  Qed.

  Lemma rqDownRsUpDisj_parent_down_children:
    forall eouts,
      Forall (fun eout => exists oidx, RqDownRsUpIdx oidx eout) eouts ->
      RqDownRsUpDisj eouts ->
      forall oidx pmsg routs rss P,
        In pmsg eouts ->
        RqDownRsUpIdx oidx pmsg ->
        NoDup (idsOf routs) ->
        RqRsDownMatch dtr oidx (idsOf routs) rss P ->
        RqDownRsUpDisj (removeOnce (id_dec msg_dec) pmsg eouts ++ routs).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    apply rqDownRsUpDisj_app;
      [apply rqDownRsUpDisj_removeOnce; auto
      |eapply rqDownRsUpDisj_down_children; eauto|].

    intros.
    apply removeOnce_In_NoDup in H8;
      [dest|apply idsOf_NoDup, rqDownRsUpDisj_NoDup; auto].
    assert (parentIdxOf dtr oidx2 = Some oidx).
    { apply in_map with (f:= idOf) in H10.
      eapply RqRsDownMatch_rq_rs in H7; [|eassumption].
      destruct H7 as [cidx [rsUp ?]]; dest.
      destruct H11.
      { disc_rule_conds. }
      { disc_rule_conds; solve_midx_false. }
    }

    split.
    - intro Hx.
      eapply subtreeIndsOf_child_SubList in Hx; [|apply Hrrs|eassumption].
      eapply rqDownRsUpDisj_in_spec
        with (eout1:= eout1) (eout2:= pmsg); try eassumption.
    - assert (~ In oidx (subtreeIndsOf dtr oidx1))
        by (eapply rqDownRsUpDisj_in_spec
              with (eout1:= pmsg) (eout2:= eout1); eauto).
      intro Hx; elim H14; clear H14.
      eapply inside_parent_in; [apply Hrrs|..]; try eassumption.
      intro; subst.
      apply subtreeIndsOf_child_in in H13; [|apply Hrrs].
      eapply rqDownRsUpDisj_in_spec with (eout1:= eout1) (eout2:= pmsg); eauto.
  Qed.

  Lemma rqDownRsUpDisj_children_up_parent:
    forall eouts,
      Forall (fun eout => exists oidx, RqDownRsUpIdx oidx eout) eouts ->
      RqDownRsUpDisj eouts ->
      forall oidx rins pmsg rqTos rssFrom P,
        RqDownRsUpIdx oidx pmsg ->
        idsOf rins = map fst rssFrom ->
        NoDup (idsOf rins) ->
        Forall (fun rin => msg_type (valOf rin) = MRs) rins ->
        SubList rins eouts ->
        RqRsDownMatch dtr oidx rqTos rssFrom P ->
        Forall (fun reout =>
                  forall ridx,
                    RqDownRsUpIdx ridx reout ->
                    ~ In ridx (subtreeIndsOf dtr oidx))
               (removeL (id_dec msg_dec) eouts rins) ->
        RqDownRsUpDisj (removeL (id_dec msg_dec) eouts rins ++ [pmsg]).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    apply rqDownRsUpDisj_app;
      [apply rqDownRsUpDisj_removeL; auto
      |apply rqDownRsUpDisj_singleton|].

    intros; dest_in.
    rewrite Forall_forall in H10; specialize (H10 _ H11 _ H12).
    eapply rqDownRsUpIdx_oidx_eq in H4; [|eassumption]; subst.

    split; [assumption|].
    assert (exists rin, In rin rins).
    { red in H9; dest.
      destruct rins.
      { exfalso; destruct rqTos; [auto|].
        apply eq_sym, map_eq_nil in H5; subst.
        discriminate.
      }
      { eexists; left; reflexivity. }
    }
    destruct H4 as [rin ?].
    pose proof H4; apply in_map with (f:= idOf) in H13.
    setoid_rewrite H5 in H13.
    eapply RqRsDownMatch_rs_rq in H9; [|eassumption].
    destruct H9 as [cidx [down ?]]; dest.
    rewrite Forall_forall in H7; specialize (H7 _ H4).
    apply H8 in H4.
    apply removeL_In_2 in H11.

    eapply outside_parent_out; [apply Hrrs| |eassumption].
    eapply rqDownRsUpDisj_in_spec with (eout1:= rin) (eout2:= eout1); eauto.
    - intro Hx; subst.
      destruct H12; [disc_rule_conds; solve_midx_false|].
      disc_rule_conds.
      elim H10; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
    - right; red; auto.
  Qed.

  Lemma disjExceptUpLocked_no_UpLockedNew_disj:
    forall oinds orqs1 orqs2 tidx,
      DisjExceptUpLocked oinds orqs1 orqs2 tidx ->
      Forall (fun oidx => ~ UpLockedNew orqs1 orqs2 oidx) oinds ->
      DisjList oinds (subtreeIndsOf dtr tidx).
  Proof.
    unfold DisjExceptUpLocked; intros.
    apply (DisjList_false_spec idx_dec).
    intros oidx ? ?.
    rewrite Forall_forall in H0.
    specialize (H0 _ H1).
    specialize (H _ H1).
    eapply H; eauto.
  Qed.

  Lemma step_NonRqUp_no_new_uplocks:
    forall st1 oidx ridx rins routs st2,
      Reachable (steps step_m) sys st1 ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      NonRqUpL dtr (RlblInt oidx ridx rins routs) ->
      ~ UpLockedNew st1.(st_orqs) st2.(st_orqs) oidx.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok Hiorqs H0 H2).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule; simpl in *.

    - disc_rule_conds.
      + intro Hx; red in Hx; repeat (simpl in Hx; mred).
      + intro Hx; red in Hx; repeat (simpl in Hx; mred).

    - disc_rule_conds.
      intro Hx; red in Hx; repeat (simpl in Hx; mred).
      dest; congruence.

    - disc_rule_conds.
      + pose proof (rqEdgeUpFrom_Some (proj1 (proj2 H)) _ H6).
        destruct H8 as [rsUp [down [pidx ?]]]; dest.
        elim (H4 pidx).
        red; do 2 eexists; eauto.
      + pose proof (rqEdgeUpFrom_Some (proj1 (proj2 H)) _ H6).
        destruct H15 as [rsUp [down [pidx ?]]]; dest.
        elim (H4 pidx).
        red; do 2 eexists; eauto.
      + intro Hx; red in Hx; repeat (simpl in Hx; mred).
      + intro Hx; red in Hx; repeat (simpl in Hx; mred).
      + intro Hx; red in Hx; repeat (simpl in Hx; mred).

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      all: intro Hx; red in Hx; repeat (simpl in Hx; mred).

    - disc_rule_conds.
      intro Hx; red in Hx; repeat (simpl in Hx; mred).
  Qed.

  Lemma upLockedNew_not_refl:
    forall orqs oidx,
      ~ UpLockedNew orqs orqs oidx.
  Proof.
    intros; intro Hx; red in Hx.
    destruct (orqs@[oidx]); simpl in *; auto.
    dest; auto.
  Qed.

  Lemma upLockedNew_not_trans:
    forall orqs1 orqs2 orqs3 oidx,
      ~ UpLockedNew orqs1 orqs2 oidx ->
      ~ UpLockedNew orqs2 orqs3 oidx ->
      ~ UpLockedNew orqs1 orqs3 oidx.
  Proof.
    unfold UpLockedNew; intros; intro Hx.
    destruct (orqs3@[oidx]) as [orq3|]; simpl in *; dest; auto.
    destruct (orqs2@[oidx]) as [orq2|]; simpl in *; dest.
    - destruct (orq2@[upRq]) as [rqiu2|]; simpl in *.
      + elim H; auto.
      + elim H0; auto.
    - elim H0; auto.
  Qed.

  Lemma step_not_in_history_no_new_uplocks:
    forall st1 oidx ridx rins routs st2 uidx,
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      uidx <> oidx ->
      ~ UpLockedNew st1.(st_orqs) st2.(st_orqs) uidx.
  Proof.
    intros.
    inv H; simpl in *.
    intro Hx; red in Hx; mred.
    destruct (orqs@[uidx]); simpl in *; auto.
    dest; auto.
  Qed.

  Lemma steps_not_in_history_no_new_uplocks:
    forall st1 hst st2 oidx,
      steps step_m sys st1 hst st2 ->
      ~ In oidx (oindsOf hst) ->
      ~ UpLockedNew st1.(st_orqs) st2.(st_orqs) oidx.
  Proof.
    induction 1; simpl; intros; [apply upLockedNew_not_refl|].
    destruct lbl; try (inv H0; simpl in *; auto; fail).
    simpl in *.
    eapply upLockedNew_not_trans.
    - eapply IHsteps; eauto.
    - eapply step_not_in_history_no_new_uplocks.
      + apply H0.
      + auto.
  Qed.

  Lemma upLockedNew_index_eq_1:
    forall orqs orqs1 orqs2 oidx,
      orqs1@[oidx] = orqs2@[oidx] ->
      (UpLockedNew orqs orqs1 oidx <-> UpLockedNew orqs orqs2 oidx).
  Proof.
    unfold UpLockedNew; intros.
    rewrite H; intuition idtac.
  Qed.

  Lemma upLockedNew_index_eq_2:
    forall orqs orqs1 orqs2 oidx,
      orqs1@[oidx] = orqs2@[oidx] ->
      (UpLockedNew orqs1 orqs oidx <-> UpLockedNew orqs2 orqs oidx).
  Proof.
    unfold UpLockedNew; intros.
    rewrite H; intuition idtac.
  Qed.

  Lemma upLockedNew_UpLocked:
    forall orqs1 orqs2 oidx,
      UpLockedNew orqs1 orqs2 oidx ->
      UpLocked orqs2 oidx.
  Proof.
    unfold UpLockedNew, UpLocked; intros.
    destruct (orqs2@[oidx]); simpl in *; dest; auto.
  Qed.

  Lemma atomic_NonRqUp_no_new_uplocks:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      Forall (NonRqUpL dtr) hst ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        Forall (fun oidx => ~ UpLockedNew s1.(st_orqs) s2.(st_orqs) oidx)
               (oindsOf hst).
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst.
    - inv_steps; inv H2; clear H7.
      repeat constructor.
      eapply step_NonRqUp_no_new_uplocks; eauto.
    - inv_steps; inv H8.
      specialize (IHAtomic H10 _ _ H9 H11).
      constructor.
      + destruct (in_dec idx_dec oidx (oindsOf hst)).
        * intros; intro Hx.
          rewrite Forall_forall in IHAtomic.
          specialize (IHAtomic _ i).
          eapply upLockedNew_not_trans; eauto.
          eapply step_NonRqUp_no_new_uplocks; eauto.
        * pose proof H11.
          eapply steps_locks_unaffected in H5; [|eassumption].
          intros; intro Hx.
          rewrite upLockedNew_index_eq_2 in Hx; [|eassumption].
          eapply step_NonRqUp_no_new_uplocks with (st1:= st2); eauto.
      + apply Forall_forall; intros uidx ?.
        rewrite Forall_forall in IHAtomic; specialize (IHAtomic _ H5).
        destruct (idx_dec uidx oidx); subst.
        * eapply upLockedNew_not_trans; eauto.
          eapply step_NonRqUp_no_new_uplocks; eauto.
        * intros; intro Hx.
          elim IHAtomic.
          rewrite upLockedNew_index_eq_1; [eassumption|].
          eapply steps_locks_unaffected.
          { eapply steps_singleton; eassumption. }
          { simpl; intros; intuition auto. }
  Qed.

  Lemma upLockedBound_OutsideUpLocked:
    forall oinds orqs1 orqs2 tidx,
      UpLockedBound oinds orqs1 orqs2 tidx ->
      forall oidx,
        ~ In oidx (subtreeIndsOf dtr tidx) ->
        OutsideUpLocked oinds orqs1 orqs2 oidx.
  Proof.
    unfold UpLockedBound, OutsideUpLocked; intros.
    specialize (H _ H1 H2).
    intro Hx.
    apply subtreeIndsOf_SubList in H; [|apply Hrrs].
    auto.
  Qed.

  Lemma rqDown_rsUp_inv_msg:
    forall orqs1 orqs2 oinds eouts,
      Forall (fun eout =>
                exists oidx,
                  RqDownMsgOutInv oinds orqs1 orqs2 oidx eout \/
                  RsUpMsgOutInv oinds orqs1 orqs2 oidx eout) eouts ->
      Forall (fun eout => exists oidx, RqDownRsUpIdx oidx eout) eouts.
  Proof.
    induction eouts; simpl; intros; [constructor|].
    inv H.
    constructor; auto.
    destruct H2 as [oidx ?].
    exists oidx.
    destruct H.
    - left; apply H.
    - right; apply H.
  Qed.

  Lemma rqDown_rsUp_inv_rqDown:
    forall orqs1 orqs2 oinds eouts,
      Forall (fun eout =>
                exists oidx,
                  RqDownMsgOutInv oinds orqs1 orqs2 oidx eout \/
                  RsUpMsgOutInv oinds orqs1 orqs2 oidx eout) eouts ->
      forall oidx rqDown,
        In rqDown eouts ->
        RqDownMsgTo oidx rqDown ->
        RqDownMsgOutInv oinds orqs1 orqs2 oidx rqDown.
  Proof.
    intros.
    rewrite Forall_forall in H.
    specialize (H _ H0).
    destruct H as [roidx ?].
    destruct H.
    - red in H; dest.
      red in H, H1; dest.
      destruct Hrrs; disc_rule_conds.
      red; repeat ssplit; try assumption.
      red; auto.
    - exfalso.
      red in H; dest.
      red in H, H1; dest.
      rewrite H in H1; discriminate.
  Qed.

  Lemma rqDown_rsUp_inv_rsUp:
    forall orqs1 orqs2 oinds eouts,
      Forall (fun eout =>
                exists oidx,
                  RqDownMsgOutInv oinds orqs1 orqs2 oidx eout \/
                  RsUpMsgOutInv oinds orqs1 orqs2 oidx eout) eouts ->
      forall oidx rsUp,
        In rsUp eouts ->
        RsUpMsgFrom oidx rsUp ->
        RsUpMsgOutInv oinds orqs1 orqs2 oidx rsUp.
  Proof.
    intros.
    rewrite Forall_forall in H.
    specialize (H _ H0).
    destruct H as [roidx ?].
    destruct H.
    - exfalso.
      red in H; dest.
      red in H, H1; dest.
      rewrite H in H1; discriminate.
    - red in H; dest.
      red in H, H1; dest.
      destruct Hrrs; disc_rule_conds.
      red; repeat ssplit; try assumption.
      red; auto.
  Qed.

  Lemma rqDown_no_rqDown:
    forall eouts,
      Forall (fun eout => exists oidx, RqDownRsUpIdx oidx eout) eouts ->
      RqDownRsUpDisj eouts ->
      forall oidx rqdm,
        RqDownMsgTo oidx rqdm ->
        In rqdm eouts ->
        forall ooidx orqdm,
          RqDownMsgTo ooidx orqdm ->
          In orqdm eouts -> orqdm <> rqdm ->
          ~ In ooidx (subtreeIndsOf dtr oidx).
  Proof.
    intros.
    pose proof (rqDownRsUpDisj_NoDup H H0).

    pose proof (In_nth_error _ _ H2).
    destruct H7 as [rn ?].
    pose proof (In_nth_error _ _ H4).
    destruct H8 as [on ?].
    eapply H0 with (n1:= on) (n2:= rn); try eassumption.
    - intro Hx; subst; congruence.
    - left; assumption.
    - left; assumption.
  Qed.

  Lemma rqDown_no_rsUp:
    forall eouts,
      Forall (fun eout => exists oidx, RqDownRsUpIdx oidx eout) eouts ->
      RqDownRsUpDisj eouts ->
      forall oidx rqdm,
        RqDownMsgTo oidx rqdm ->
        In rqdm eouts ->
        forall ooidx orsum,
          RsUpMsgFrom ooidx orsum ->
          In orsum eouts ->
          ~ In ooidx (subtreeIndsOf dtr oidx).
  Proof.
    intros.
    pose proof (rqDownRsUpDisj_NoDup H H0).

    pose proof (In_nth_error _ _ H2).
    destruct H6 as [rn ?].
    pose proof (In_nth_error _ _ H4).
    destruct H7 as [on ?].
    eapply H0 with (n1:= on) (n2:= rn); try eassumption.
    - intro Hx; subst.
      rewrite H6 in H7; inv H7.
      disc_rule_conds.
    - right; assumption.
    - left; assumption.
  Qed.

  Lemma rsUp_no_rqDown:
    forall eouts,
      Forall (fun eout => exists oidx, RqDownRsUpIdx oidx eout) eouts ->
      RqDownRsUpDisj eouts ->
      forall oidx rsum,
        RsUpMsgFrom oidx rsum ->
        In rsum eouts ->
        forall ooidx orqdm,
          RqDownMsgTo ooidx orqdm ->
          In orqdm eouts ->
          ~ In ooidx (subtreeIndsOf dtr oidx).
  Proof.
    intros.
    pose proof (rqDownRsUpDisj_NoDup H H0).

    pose proof (In_nth_error _ _ H2).
    destruct H6 as [rn ?].
    pose proof (In_nth_error _ _ H4).
    destruct H7 as [on ?].
    eapply H0 with (n1:= on) (n2:= rn); try eassumption.
    - intro Hx; subst.
      rewrite H6 in H7; inv H7.
      disc_rule_conds.
    - left; assumption.
    - right; assumption.
  Qed.

  Lemma rsUp_no_rsUp:
    forall eouts,
      Forall (fun eout => exists oidx, RqDownRsUpIdx oidx eout) eouts ->
      RqDownRsUpDisj eouts ->
      forall oidx rsum,
        RsUpMsgFrom oidx rsum ->
        In rsum eouts ->
        forall ooidx orsum,
          RsUpMsgFrom ooidx orsum ->
          In orsum eouts -> rsum <> orsum ->
          ~ In ooidx (subtreeIndsOf dtr oidx).
  Proof.
    intros.
    pose proof (rqDownRsUpDisj_NoDup H H0).

    pose proof (In_nth_error _ _ H2).
    destruct H7 as [rn ?].
    pose proof (In_nth_error _ _ H4).
    destruct H8 as [on ?].
    eapply H0 with (n1:= on) (n2:= rn); try eassumption.
    - intro Hx; subst; congruence.
    - right; assumption.
    - right; assumption.
  Qed.

  Lemma disjExceptUpLocked_history_add:
    forall oinds orqs1 orqs2 rcidx,
      DisjExceptUpLocked oinds orqs1 orqs2 rcidx ->
      forall oidx,
        ~ In oidx (subtreeIndsOf dtr rcidx) ->
        DisjExceptUpLocked (oidx :: oinds) orqs1 orqs2 rcidx.
  Proof.
    unfold DisjExceptUpLocked; intros.
    dest_in; auto.
  Qed.

  Lemma disjExceptUpLocked_child:
    forall oinds orqs1 orqs2 oidx,
      DisjExceptUpLocked oinds orqs1 orqs2 oidx ->
      forall cidx orq,
        parentIdxOf dtr cidx = Some oidx ->
        DisjExceptUpLocked (oidx :: oinds) orqs1 (orqs2 +[oidx <- orq]) cidx.
  Proof.
    unfold DisjExceptUpLocked; intros.
    icase oidx0; [apply parent_not_in_subtree; [apply Hrrs|]; assumption|].
    specialize (H _ H1); clear H1.
    apply subtreeIndsOf_child_SubList in H0; [|apply Hrrs].
    intro Hx; apply H0 in Hx.
    eapply H; eauto.
    clear Hx; intro Hx; elim H2.
    eapply upLockedNew_index_eq_1; [|eassumption].
    mred.
  Qed.

  Lemma upLockCoverInv_child:
    forall oinds orqs oidx,
      UpLockCoverInv oinds orqs oidx ->
      forall cidx orq,
        parentIdxOf dtr cidx = Some oidx ->
        UpLockCoverInv (oidx :: oinds) (orqs +[oidx <- orq]) cidx.
  Proof.
    unfold UpLockCoverInv; intros.
    icase oidx0.
    - exfalso.
      eapply parent_not_in_subtree with (oidx:= cidx);
        [apply Hrrs|..]; eassumption.
    - mred.
      apply subtreeIndsOf_child_SubList in H0; [|apply Hrrs].
      apply H0 in H1.
      specialize (H _ H1 H2 _ _ H3 H4 _ _ H5 H6 H7).
      apply (DisjList_cons_inv idx_dec); auto.
      intro Hx.
      apply subtreeIndsOf_child_SubList in H5; [|apply Hrrs].
      apply H5 in Hx.
      eapply subtreeIndsOf_In_each_other_eq in Hx; try apply Hrrs; eauto.
  Qed.

  Lemma upLockedBound_child:
    forall oinds orqs1 orqs2 pidx cidx orq2 rqiu norq
           (Hsep: ~ In pidx oinds -> DisjList oinds (subtreeIndsOf dtr pidx)),
      UpLockedBound oinds orqs1 orqs2 pidx ->
      UpLockCoverInv oinds orqs2 pidx ->
      orqs2@[pidx] = Some orq2 ->
      orq2@[upRq] = Some rqiu ->
      parentIdxOf dtr cidx = Some pidx ->
      edgeDownTo dtr cidx = rqiu.(rqi_midx_rsb) ->
      norq@[upRq] = None ->
      UpLockedBound (pidx :: oinds) orqs1 (orqs2 +[pidx <- norq]) cidx.
  Proof.
    destruct Hrrs as [? [? ?]]; intros; red; intros.
    icase oidx; [simpl_locks|].
    destruct (in_dec idx_dec pidx oinds).
    - assert (In pidx (subtreeIndsOf dtr pidx))
        by (eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption]).
      specialize (H3 _ H11 i _ _ H4 H5); clear H11.
      red in H10; mred.
      specialize (H2 _ H9 H10).
      apply subtreeIndsOf_composed in H2; [|apply Hrrs]; destruct H2;
        [subst; exfalso; auto|].
      destruct H2 as [rcidx [? ?]].
      pose proof (parentIdxOf_Some (proj1 (proj2 H)) _ H2).
      destruct H12 as [rqUp [rsUp [down ?]]]; dest.
      destruct (option_dec idx_dec (rqi_midx_rsb rqiu) (Some down)); [subst; disc_rule_conds|].
      specialize (H3 _ _ H2 H14 n0).
      exfalso; destruct (H3 oidx); auto.
    - exfalso.
      apply Hsep in n0.
      red in H10; mred.
      specialize (H2 _ H9 H10).
      destruct (n0 oidx); auto.
  Qed.

  Lemma noDownLockOutside_child_in:
    forall oinds orqs1 orqs2 oidx,
      In oidx oinds ->
      NoDownLockOutside oinds orqs2 oidx ->
      forall cidx down,
        parentIdxOf dtr cidx = Some oidx ->
        edgeDownTo dtr cidx = Some down ->
        (* Below is the general condition that covers
         * both [RsDownDown] and [RsUpDown] *)
        (forall ocidx odown,
            parentIdxOf dtr ocidx = Some oidx ->
            edgeDownTo dtr ocidx = Some odown ->
            odown <> down ->
            NoLocks2 oinds orqs1 orqs2 (subtreeIndsOf dtr ocidx) \/
            DisjList oinds (subtreeIndsOf dtr ocidx)) ->
        forall norq,
          norq@[downRq] = None ->
          NoDownLockOutside (oidx :: oinds) (orqs2 +[oidx <- norq]) cidx.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    red; intros.
    icase oidx0; [simpl_locks|].
    red; mred.
    destruct (in_dec idx_dec oidx0 (subtreeIndsOf dtr oidx));
      [|apply H3; auto].
    eapply subtreeIndsOf_composed in i; [|apply Hrrs].
    destruct i; [exfalso; auto|].
    destruct H10 as [rcidx [? ?]].
    destruct (idx_dec rcidx cidx); subst; [exfalso; auto|].
    pose proof (parentIdxOf_Some (proj1 (proj2 H)) _ H10).
    destruct H12 as [rrqUp [rrsUp [rdown ?]]]; dest.
    assert (rdown <> down).
    { intro Hx; subst; disc_rule_conds; auto. }
    specialize (H6 _ _ H10 H14 H15); destruct H6.
    - apply H6; assumption.
    - exfalso; destruct (H6 oidx0); auto.
  Qed.

  Lemma noDownLockOutside_child_in_1:
    forall oinds orqs oidx,
      In oidx oinds ->
      NoDownLockOutside oinds orqs oidx ->
      UpLockCoverInv oinds orqs oidx ->
      forall cidx down porq norq rqiu,
        parentIdxOf dtr cidx = Some oidx ->
        edgeDownTo dtr cidx = Some down ->
        orqs@[oidx] = Some porq ->
        porq@[upRq] = Some rqiu ->
        rqiu.(rqi_midx_rsb) = Some down ->
        norq@[downRq] = None ->
        NoDownLockOutside (oidx :: oinds) (orqs +[oidx <- norq]) cidx.
  Proof.
    intros; subst.
    eapply noDownLockOutside_child_in with (orqs1:= M.empty _); eauto.
    intros.
    assert (In oidx (subtreeIndsOf dtr oidx)).
    { eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption]. }
    red in H1.
    right; eapply H1; eauto.
    congruence.
  Qed.

  Lemma noDownLockOutside_child_out:
    forall oinds orqs oidx,
      DisjList oinds (subtreeIndsOf dtr oidx) ->
      NoDownLockOutside oinds orqs oidx ->
      forall cidx norq,
        parentIdxOf dtr cidx = Some oidx ->
        norq@[downRq] = None ->
        NoDownLockOutside (oidx :: oinds) (orqs +[oidx <- norq]) cidx.
  Proof.
    intros.
    red; intros.
    icase oidx0; simpl_locks.
    apply H0; auto.
    eapply DisjList_In_2; eauto.
  Qed.

  Lemma rsUp_outs_case_isolated:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      forall st1 st2,
        Reachable (steps step_m) sys st1 ->
        steps step_m sys st1 hst st2 ->
        forall rsFrom rsfm cidx,
          Forall (fun eout => exists oidx, RqDownRsUpIdx oidx eout) eouts ->
          RqDownRsUpDisj eouts ->
          In (rsFrom, rsfm) eouts ->
          rsEdgeUpFrom dtr cidx = Some rsFrom ->
          In cidx (oindsOf hst) ->
          SubList (oindsOf hst) (subtreeIndsOf dtr cidx) ->
          eouts = [(rsFrom, rsfm)].
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (rqDownRsUpDisj_NoDup H5 H6).
    pose proof (In_nth_error _ _ H7).
    destruct H12 as [rn ?].
    assert (eouts = [(rsFrom, rsfm)] \/
            exists mn idm,
              nth_error eouts mn = Some idm /\
              mn <> rn).
    { destruct eouts as [|eout0 teouts]; [elim H7|].
      destruct teouts as [|eout1 teouts]; [dest_in; left; reflexivity|].
      right; inv H7.
      { destruct eout1 as [midx msg].
        exists 1, (midx, msg); split; [intuition|].
        intro Hx; subst.
        inv H11; inv H12.
        elim H14; left; reflexivity.
      }
      { inv H13.
        { destruct eout0 as [midx msg].
          exists 0, (midx, msg); split; [intuition|].
          intro Hx; subst.
          inv H11; inv H12.
          elim H14; left; reflexivity.
        }
        { destruct eout1 as [midx msg].
          exists 1, (midx, msg); split; [intuition|].
          intro Hx; subst.
          inv H11; inv H12; inv H16.
          elim H13; apply in_map_iff.
          exists (rsFrom, rsfm); auto.
        }
      }
    }

    destruct H13; [auto|exfalso].
    destruct H13 as [mn [idm [? ?]]].
    rewrite Forall_forall in H5.
    pose proof (nth_error_In _ _ H12).
    pose proof (H5 _ H15).
    destruct H16 as [roidx ?].
    pose proof (nth_error_In _ _ H13).
    pose proof (H5 _ H17).
    destruct H18 as [oidx ?].

    elim (H6 _ _ _ _ _ _ H14 H13 H18 H12 H16).
    destruct H16; [destruct H16; disc_rule_conds; solve_midx_false|].
    destruct H16; disc_rule_conds.

    destruct H18.
    - destruct H18.
      pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H19).
      destruct H20 as [rqUp [rsUp [pidx ?]]]; dest.
      apply in_map with (f:= idOf) in H17.
      pose proof (atomic_down_out_in_history Hiorqs Hrrs H2 H3 H4 _ H19 H22 H17).
      eapply inside_child_in; [apply Hrrs|..]; eauto.
    - destruct H18.
      pose proof (rsEdgeUpFrom_Some (proj1 (proj2 H)) _ H19).
      apply in_map with (f:= idOf) in H17.
      pose proof (atomic_rsUp_out_in_history Hiorqs Hrrs H2 H3 H4 _ H19 H17).
      auto.
  Qed.

  Lemma rsUp_no_other_messages_in:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      forall st1 st2,
        Reachable (steps step_m) sys st1 ->
        steps step_m sys st1 hst st2 ->
        forall rins rqTos P oidx orq rqid,
          NoDup (idsOf rins) ->
          Forall (fun rin => msg_type (valOf rin) = MRs) rins ->
          SubList rins eouts ->

          In oidx (oindsOf hst) ->
          RqRsDownMatch dtr oidx rqTos rqid.(rqi_rss) P ->
          (st_orqs st2)@[oidx] = Some orq -> orq@[downRq] = Some rqid ->
          DownLockCoverInv (oindsOf hst) oidx rqid ->
          (rsEdgeUpFrom dtr oidx = rqid.(rqi_midx_rsb) \/ rqid.(rqi_midx_rsb) = None) ->
          idsOf rins = map fst rqid.(rqi_rss) ->

          Forall (fun eout => exists oidx, RqDownRsUpIdx oidx eout) eouts ->
          RqDownRsUpDisj eouts ->
          Forall (fun reout =>
                    forall ridx,
                      RqDownRsUpIdx ridx reout ->
                      ~ In ridx (subtreeIndsOf dtr oidx))
                 (removeL (id_dec msg_dec) eouts rins).
  Proof.
    destruct Hrrs as [? [? [_ ?]]]; intros.
    rewrite Forall_forall.
    intros [rmidx rmsg]; intros.
    intro Hx; apply subtreeIndsOf_composed in Hx; [|apply Hrrs].

    destruct Hx; subst.
    - assert (exists rin, In rin rins).
      { red in H9; dest.
        destruct rins.
        { exfalso; destruct rqTos; [auto|].
          apply eq_sym, map_eq_nil in H14.
          rewrite H14 in H19; discriminate.
        }
        { eexists; left; reflexivity. }
      }
      destruct H19 as [[rsUp rsm] ?].
      pose proof H19.
      apply in_map with (f:= idOf) in H20.
      setoid_rewrite H14 in H20.
      eapply RqRsDownMatch_rs_rq in H9; [|eassumption]; clear H20.
      destruct H9 as [cidx [down ?]]; dest; simpl in *.
      rewrite Forall_forall in H6; specialize (H6 _ H19).
      apply removeL_In_2 in H17.
      eapply rqDownRsUpDisj_in_spec
        with (eout1:= (rsUp, rsm)) (eout2:= (rmidx, rmsg)); eauto.
      + intro Hx; inv Hx.
        destruct H18; disc_rule_conds.
        apply parentIdxOf_not_eq in H20; [auto|apply Hrrs].
      + right; red; eauto.
      + eapply subtreeIndsOf_child_in; [apply Hrrs|assumption].

    - destruct H19 as [cidx [? ?]].
      pose proof (parentIdxOf_Some (proj1 (proj2 H)) _ H19).
      destruct H21 as [rqUp [rsUp [down ?]]]; dest.

      destruct (in_dec idx_dec rsUp (idsOf rins)).
      + apply in_map_iff in i; destruct i as [[rsUp' rsum] [? ?]].
        simpl in *; subst.
        eapply rqDownRsUpDisj_in_spec
          with (eout1:= (rmidx, rmsg)) (eout2:= (rsUp, rsum)); try eassumption.
        * eapply removeL_In_2; eassumption.
        * apply H7; assumption.
        * apply removeL_In_NoDup in H17;
            [dest|apply idsOf_NoDup, rqDownRsUpDisj_NoDup; assumption].
          intro Hx; inv Hx; auto.
        * rewrite Forall_forall in H6; specialize (H6 _ H25).
          right; red; auto.

      + rewrite H14 in n.
        assert (rqi_midx_rsb rqid <> Some down)
          by (intro Hx; rewrite Hx in *;
              destruct H13; [solve_midx_false|discriminate]).
        specialize (H12 _ _ _ H19 H22 H23 n H24); clear H24.

        destruct H18.
        * disc_rule_conds.
          pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H24).
          destruct H25 as [rrqUp [rrsUp [rpidx ?]]]; dest.
          apply removeL_In_2 in H17.
          pose proof H17.
          apply in_map with (f:= idOf) in H28.
          pose proof (atomic_down_out_in_history Hiorqs Hrrs H2 H3 H4 _ H24 H27 H28); clear H28.
          eapply DisjList_In_2 in H29; [|eassumption].
          elim H29.
          eapply inside_parent_in; [apply Hrrs|..]; try eassumption.

          intro Hx; subst; disc_rule_conds.
          pose proof (downLockInv_ok Hiorqs H0 H H1 (reachable_steps H3 H4)).
          pose proof (steps_object_in_system H4 _ H8).
          destruct H25 as [obj [? ?]]; subst.
          good_locking_get obj.

          eapply downLockInvORq_down_rqsQ_length_one_locked
            with (cidx0:= cidx) in H26; try eassumption.
          { destruct H26 as [rrqid ?]; dest.
            mred; disc_rule_conds; auto.
          }
          { apply rqsQ_length_ge_one with (msg:= rmsg); auto.
            pose proof (atomic_messages_eouts_in H2 H4).
            rewrite Forall_forall in H27; specialize (H27 _ H17).
            assumption.
          }

        * disc_rule_conds.
          apply removeL_In_2 in H17.
          pose proof H17.
          apply in_map with (f:= idOf) in H25.
          pose proof (atomic_rsUp_out_in_history Hiorqs Hrrs H2 H3 H4 _ H24 H25); clear H25.
          eapply DisjList_In_2 in H26; [|eassumption].
          auto.
  Qed.

  Lemma rsUp_outs_case_back:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      forall st1 st2,
        Reachable (steps step_m) sys st1 ->
        steps step_m sys st1 hst st2 ->
        forall rins rqTos P roidx rcidx rorq rqid,
          NoDup (idsOf rins) ->
          Forall (fun rin => msg_type (valOf rin) = MRs) rins ->
          SubList rins eouts ->

          Forall (fun eout => exists oidx, RqDownRsUpIdx oidx eout) eouts ->
          RqDownRsUpDisj eouts ->

          In roidx (oindsOf hst) ->
          RqRsDownMatch dtr roidx rqTos rqid.(rqi_rss) P ->
          (st_orqs st2)@[roidx] = Some rorq -> rorq@[downRq] = Some rqid ->
          DownLockCoverInv (oindsOf hst) roidx rqid ->
          idsOf rins = map fst rqid.(rqi_rss) ->

          DownLockRoot (oindsOf hst) (st_orqs st1) (st_orqs st2)
                       roidx rqid (Some rcidx) ->
          DownLockCoverInv (oindsOf hst) roidx rqid ->
          OutsInRoot roidx (Some rcidx) eouts ->
          SubList eouts rins.
  Proof.
    destruct Hrrs as [? [? [_ ?]]]; intros.
    red; intros [rmidx rmsg]; intros.
    red in H18; rewrite Forall_forall in H18.
    specialize (H18 _ H19).
    destruct H18.
    rewrite Forall_forall in H8; specialize (H8 _ H19).
    destruct H8 as [oidx ?].
    red in H16; dest.

    assert (exists pidx,
               parentIdxOf dtr oidx = Some pidx /\
               In pidx (subtreeIndsOf dtr roidx) /\
               ~ In oidx (subtreeIndsOf dtr rcidx)).
    { destruct H8.
      { clear H20.
        pose proof H8; destruct H20; simpl in *.
        pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H25).
        destruct H26 as [rqUp [rsUp [pidx ?]]]; dest.
        eauto.
      }
      { clear H18.
        pose proof H8; destruct H18; simpl in *.
        pose proof (rsEdgeUpFrom_Some (proj1 (proj2 H)) _ H25).
        destruct H26 as [rqUp [down [pidx ?]]]; dest.
        eauto.
      }
    }
    destruct H25 as [pidx ?]; dest.
    apply subtreeIndsOf_composed in H26; [|apply Hrrs].
    destruct H26; subst.

    - (** case message-from-the-root *)
      destruct H8.
      + (** case RqDown *)
        exfalso; clear H20.
        destruct H8; simpl in *.
        pose proof (parentIdxOf_Some (proj1 (proj2 H)) _ H25).
        destruct H26 as [rqUp [rsUp [down ?]]]; dest.
        disc_rule_conds.
        pose proof (steps_object_in_system H4 _ H10).
        destruct H29 as [robj [? ?]]; subst.
        pose proof (downLockInv_ok Hiorqs H0 H H1 (reachable_steps H3 H4)).
        good_locking_get robj.

        destruct (in_dec idx_dec rsUp (map fst rqid.(rqi_rss))).
        * (* case RqDown-in-responses *)
          eapply downLockInvORq_down_rqsQ_rsUp_False
            with (cidx:= oidx) in H31; try eassumption.
          { eapply rqsQ_length_ge_one with (msg:= rmsg); auto.
            pose proof (atomic_messages_eouts_in H2 H4).
            rewrite Forall_forall in H32; specialize (H32 _ H19).
            assumption.
          }
          { eapply RqRsDownMatch_rs_rq in H11; [|eassumption].
            destruct H11 as [cidx [rdown ?]]; dest.
            rewrite <-H15 in i.
            apply in_map_iff in i; destruct i as [[rsUp' rsum] [? ?]]; simpl in *; subst.
            apply H7 in H37.
            eapply findQ_length_ge_one with (msg:= rsum); auto.
            pose proof (atomic_messages_eouts_in H2 H4).
            rewrite Forall_forall in H36; specialize (H36 _ H37).
            assumption.
          }
        * (* case RqDown-not-in-responses *)
          eapply downLockInvORq_down_rqsQ_length_one_locked
            with (cidx:= oidx) in H31; try eassumption.
          { destruct H31 as [rrqid ?]; dest.
            mred; disc_rule_conds; auto.
          }
          { apply rqsQ_length_ge_one with (msg:= rmsg); auto.
            pose proof (atomic_messages_eouts_in H2 H4).
            rewrite Forall_forall in H32; specialize (H32 _ H19).
            assumption.
          }

      + (** case RsUp *)
        clear H18.
        destruct H8; simpl in *.
        pose proof (parentIdxOf_Some (proj1 (proj2 H)) _ H25).
        destruct H26 as [rqUp [rsUp [down ?]]]; dest.
        disc_rule_conds.
        pose proof (steps_object_in_system H4 _ H10).
        destruct H28 as [robj [? ?]]; subst.
        pose proof (downLockInv_ok Hiorqs H0 H H1 (reachable_steps H3 H4)).
        good_locking_get robj.
        pose proof (atomic_messages_eouts_in H2 H4).
        rewrite Forall_forall in H32.

        destruct (in_dec idx_dec rsUp (map fst rqid.(rqi_rss))).
        * (* case RsUp-in-responses *)
          eapply RqRsDownMatch_rs_rq in H11; [|eassumption].
          destruct H11 as [cidx [rdown ?]]; dest.
          rewrite <-H15 in i.
          apply in_map_iff in i; destruct i as [[rsUp' rsum] [? ?]]; simpl in *; subst.
          destruct (msg_dec rsum rmsg); subst; auto.
          exfalso.
          eapply downLockInvORq_rsUp_length_two_False
            with (cidx0:= cidx) in H31; try eassumption.
          eapply findQ_length_two with (msg1:= rsum) (msg2:= rmsg); eauto.
          { apply H7 in H38; specialize (H32 _ H38); assumption. }
          { specialize (H32 _ H19); assumption. }
        * (* case RsUp-not-in-responses *)
          exfalso.
          eapply downLockInvORq_rsUp_length_one_locked
            with (cidx:= oidx) in H31; try eassumption.
          { destruct H31 as [rrqid ?]; dest.
            mred; disc_rule_conds; auto.
          }
          { apply findQ_length_ge_one with (msg:= rmsg); auto.
            specialize (H32 _ H19); assumption.
          }

    - (** case message-not-from-the-root *)
      exfalso.
      destruct H26 as [cidx ?]; dest.
      pose proof (parentIdxOf_Some (proj1 (proj2 H)) _ H26).
      destruct H29 as [rqUp [rsUp [down ?]]]; dest.

      destruct (in_dec idx_dec rsUp (map fst rqid.(rqi_rss))).
      + (** Case message-in-responses *)
        rewrite <-H15 in i.
        apply in_map_iff in i; destruct i as [[rsUp' rsum] [? ?]]; simpl in *; subst.
        eapply rqDownRsUpDisj_in_spec
          with (eout1:= (rmidx, rmsg)) (eout2:= (rsUp, rsum)); try eassumption.
        * apply H7; assumption.
        * intro Hx; inv Hx.
          destruct H8; [disc_rule_conds; solve_midx_false|].
          disc_rule_conds.
          eapply parent_not_in_subtree; [apply Hrrs|..]; eassumption.
        * rewrite Forall_forall in H6; specialize (H6 _ H33).
          right; red; eauto.
        * eapply inside_child_in; [apply Hrrs|..]; eassumption.

      + (** Case message-not-in-responses *)
        assert (rqi_midx_rsb rqid <> Some down).
        { intro Hx; rewrite Hx in *; disc_rule_conds.
          elim H27; eapply inside_child_in; [apply Hrrs|..]; eassumption.
        }
        specialize (H14 _ _ _ H26 H30 H31 n H32); clear H32.
        destruct H8.
        * disc_rule_conds.
          apply in_map with (f:= idOf) in H19.
          pose proof (atomic_down_out_in_history Hiorqs Hrrs H2 H3 H4 _ H32 H25 H19).
          eapply DisjList_In_2 in H33; [|eassumption].
          auto.
        * disc_rule_conds.
          apply in_map with (f:= idOf) in H19.
          pose proof (atomic_rsUp_out_in_history Hiorqs Hrrs H2 H3 H4 _ H32 H19).
          eapply DisjList_In_2 in H33; [|eassumption].
          elim H33; eapply inside_child_in; [apply Hrrs|..]; eassumption.
  Qed.

  Lemma step_msg_outs_ok:
    forall st1 st2 oidx ridx rins routs,
      Reachable (steps step_m) sys st1 ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      MsgOutsInv [oidx] st1.(st_orqs) st2.(st_orqs) routs.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok Hiorqs H0 H2).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule; simpl in *.

    - disc_rule_conds; [constructor|].
      eapply MsgOutsRsDown.
      + red; eauto.
      + red; intros; dest_in.
        apply parent_not_in_subtree; [apply Hrrs|]; assumption.
      + red; intros; dest_in; mred.
      + red; intros; dest_in; simpl_locks.
      + red; intros; dest_in; simpl_locks.

    - disc_rule_conds.
      eapply MsgOutsRqDownRsUp.
      + apply rqDownRsUpDisj_singleton.
      + repeat constructor.
        eexists; right.
        red; repeat ssplit; [red; eauto|..].
        * red; intros; dest_in.
          split; simpl_locks.
          intro Hx; dest; auto.
        * red; intros; dest_in; simpl_locks.
          dest; exfalso; auto.
      + red; intros; dest_in; simpl_locks.
      + intros; red in H3; dest; dest_in; simpl_locks.

    - disc_rule_conds.
      + eapply MsgOutsRqUp; [red; eauto|..].
        * red; intros; dest_in.
          red; apply (DisjList_singleton_1 idx_dec).
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * red; intros; dest_in.
          eapply rqEdgeUpFrom_subtreeIndsOf_self_in; [apply Hrrs|congruence].
        * apply SubList_cons; [|apply SubList_nil].
          eapply rqEdgeUpFrom_subtreeIndsOf_self_in; [apply Hrrs|congruence].
        * red; intros; dest_in; simpl_locks.
          split; [discriminate|reflexivity].
      + eapply MsgOutsRqUp; [red; eauto|..].
        * red; intros; dest_in.
          red; apply (DisjList_singleton_1 idx_dec).
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * red; intros; dest_in.
          eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption].
        * apply SubList_cons; [|apply SubList_nil].
          eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption].
        * red; intros; dest_in; simpl_locks.
          split; [discriminate|reflexivity].

      + eapply MsgOutsRqDownRsUp.
        * eapply rqDownRsUpDisj_down_children; [apply H19|eassumption].
        * apply Forall_forall; intros [midx msg] ?.
          rewrite Forall_forall in H32; specialize (H32 _ H3).
          apply in_map with (f:= idOf) in H3.
          eapply RqRsDownMatch_rq_rs in H36; [|eassumption].
          destruct H36 as [cidx [rsUp ?]]; dest.
          eexists; left.
          red; repeat ssplit; [red; eauto|..].
          { red; apply (DisjList_singleton_1 idx_dec).
            apply parent_not_in_subtree; [apply Hrrs|]; assumption.
          }
          { red; intros; dest_in; simpl_locks. }
        * red; intros; dest_in.
          red; intros.
          red; apply (DisjList_singleton_1 idx_dec).
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * intros.
          red in H3; dest; dest_in.
          destruct orcidx as [rcidx|]; dest.
          { simpl_locks.
            apply parentIdxOf_Some in H3; [|apply H].
            dest; congruence.
          }
          { repeat split; auto.
            { apply Forall_forall; intros [midx msg] ?.
              apply in_map with (f:= idOf) in H3.
              eapply RqRsDownMatch_rq_rs in H36; [|eassumption].
              destruct H36 as [cidx [rsUp ?]]; dest.
              split.
              { red; intros; disc_rule_conds.
                split; [|auto].
                eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption].
              }
              { red; intros; disc_rule_conds; solve_midx_false. }
            }
            { red; intros; dest_in.
              elim H11.
              apply RqRsDownMatch_has_child in H36; dest.
              eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption].
            }
          }

      + eapply MsgOutsRqDownRsUp.
        * eapply rqDownRsUpDisj_down_children; [apply H19|eassumption].
        * apply Forall_forall; intros [midx msg] ?.
          rewrite Forall_forall in H32; specialize (H32 _ H5).
          apply in_map with (f:= idOf) in H5.
          eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
          destruct H20 as [cidx [rsUp ?]]; dest.
          eexists; left.
          red; repeat ssplit; [red; eauto|..].
          { red; apply (DisjList_singleton_1 idx_dec).
            apply parent_not_in_subtree; [apply Hrrs|]; assumption.
          }
          { red; intros; dest_in; simpl_locks. }
        * red; intros; dest_in.
          red; intros.
          red; apply (DisjList_singleton_1 idx_dec).
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * intros.
          red in H5; dest; dest_in.
          destruct orcidx as [rcidx|]; [dest|simpl_locks; congruence].
          simpl_locks.
          red; repeat ssplit.
          { apply Forall_forall; intros [midx msg] ?.
            apply in_map with (f:= idOf) in H23.
            eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
            destruct H20 as [cidx [rsUp ?]]; dest.
            split.
            { red; intros; disc_rule_conds.
              split.
              { eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption]. }
              { eapply subtreeIndsOf_other_child_not_in;
                  [apply Hrrs|..]; eassumption.
              }
            }
            { red; intros; disc_rule_conds; solve_midx_false. }
          }
          { red; intros; dest_in.
            apply parent_not_in_subtree; [apply Hrrs|]; assumption.
          }
          { red; intros; dest_in.
            red; apply (DisjList_singleton_1 idx_dec).
            intro Hx.
            apply subtreeIndsOf_child_SubList in H31; [|apply Hrrs].
            apply H31 in Hx.
            eapply parent_not_in_subtree; [apply Hrrs|..]; eauto.
          }
          { red; intros; dest_in; simpl_locks. }
          { red; intros; dest_in.
            elim H27.
            eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption].
          }

      + eapply MsgOutsRqDownRsUp.
        * eapply rqDownRsUpDisj_down_children; [apply H19|eassumption].
        * apply Forall_forall; intros [midx msg] ?.
          rewrite Forall_forall in H32; specialize (H32 _ H7).
          apply in_map with (f:= idOf) in H7.
          eapply RqRsDownMatch_rq_rs in H6; [|eassumption].
          destruct H6 as [cidx [rsUp ?]]; dest.
          eexists; left.
          red; repeat ssplit; [red; eauto|..].
          { red; apply (DisjList_singleton_1 idx_dec).
            apply parent_not_in_subtree; [apply Hrrs|]; assumption.
          }
          { red; intros; dest_in; simpl_locks. }
        * red; intros; dest_in.
          simpl_locks.
          red; intros.
          red; apply (DisjList_singleton_1 idx_dec).
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * intros; exfalso.
          red in H7; dest; dest_in; simpl_locks.
          destruct orcidx as [rcidx|]; [dest|simpl_locks; congruence].
          rewrite H39 in *; solve_midx_false.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + eapply MsgOutsRsDown; [red; eauto|..].
        * red; intros; dest_in.
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * red; intros; dest_in.
          red; apply (DisjList_singleton_1 idx_dec).
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * red; intros; dest_in; simpl_locks.
        * red; intros; dest_in; simpl_locks.
      + constructor.
      + eapply MsgOutsRsDown; [red; eauto|..].
        * red; intros; dest_in.
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * red; intros; dest_in.
          red; apply (DisjList_singleton_1 idx_dec).
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * red; intros; dest_in; simpl_locks.
        * red; intros; dest_in; simpl_locks.

      + eapply MsgOutsRqDownRsUp.
        * apply rqDownRsUpDisj_singleton.
        * repeat constructor.
          eexists; right.
          red; repeat ssplit; [red; eauto|..].
          { red; intros; dest_in.
            split; simpl_locks.
          }
          { red; intros; dest_in; simpl_locks. }
        * red; intros; dest_in; simpl_locks.
        * intros; exfalso.
          red in H11; dest; dest_in; simpl_locks.
      + constructor.

    - disc_rule_conds.
      eapply MsgOutsRqDownRsUp.
      + eapply rqDownRsUpDisj_down_children; [apply H19|eassumption].
      + apply Forall_forall; intros [midx msg] ?.
        rewrite Forall_forall in H24; specialize (H24 _ H5).
        apply in_map with (f:= idOf) in H5.
        eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
        destruct H20 as [cidx [rsUp ?]]; dest.
        eexists; left.
        red; repeat ssplit; [red; eauto|..].
        * apply (DisjList_singleton_1 idx_dec).
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * red; intros; dest_in; simpl_locks.
      + red; intros; dest_in; simpl_locks.
        red; intros.
        apply (DisjList_singleton_1 idx_dec).
        apply parent_not_in_subtree; [apply Hrrs|]; assumption.
      + intros.
        red in H5; dest; dest_in; simpl_locks.
        destruct orcidx as [rcidx|]; [dest|simpl_locks; congruence].
        red; repeat ssplit.
        * apply Forall_forall; intros [midx msg] ?.
          apply in_map with (f:= idOf) in H25.
          eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
          destruct H20 as [cidx [rsUp ?]]; dest.
          split.
          { red; intros; disc_rule_conds.
            split.
            { eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption]. }
            { eapply subtreeIndsOf_other_child_not_in;
                [apply Hrrs|..]; eassumption.
            }
          }
          { red; intros; disc_rule_conds; solve_midx_false. }
        * red; intros; dest_in.
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * red; intros; dest_in.
          red; apply (DisjList_singleton_1 idx_dec).
          intro Hx.
          apply subtreeIndsOf_child_SubList in H30; [|apply Hrrs].
          apply H30 in Hx.
          eapply parent_not_in_subtree; [apply Hrrs|..]; eauto.
        * red; intros; dest_in; simpl_locks.
        * red; intros; dest_in.
          elim H27.
          eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption].
  Qed.

  Section InternalStep.

    Variables (st0: State)
              (inits ins: list (Id Msg)) (hst: History) (outs eouts: list (Id Msg))
              (oss: OStates) (orqs: ORqs Msg) (msgs: MessagePool Msg)
              (obj: Object) (rule: Rule)
              (post: OState) (porq: ORq Msg) (rins: list (Id Msg))
              (nost: OState) (norq: ORq Msg) (routs: list (Id Msg)).

    Hypotheses
      (Hatm: Atomic inits ins hst outs eouts)
      (Hrch: Reachable (steps step_m) sys st0)
      (Hsteps: steps step_m sys st0 hst {| st_oss := oss;
                                           st_orqs := orqs;
                                           st_msgs := msgs |})
      (Hrins: rins <> nil)
      (Hosub: SubList rins eouts)
      (Hmoc: MsgOutsInv (oindsOf hst) st0.(st_orqs) orqs eouts)
      (Hftinv: FootprintsOk dtr sys {| st_oss := oss;
                                       st_orqs := orqs;
                                       st_msgs := msgs |})
      (Hdlinv: DownLockInv dtr sys {| st_oss := oss;
                                      st_orqs := orqs;
                                      st_msgs := msgs |}).

    Hypotheses
      (HobjIn: In obj (sys_objs sys))
      (HruleIn: In rule (obj_rules obj))
      (Hporq: orqs@[obj_idx obj] = Some porq)
      (Hpost: oss@[obj_idx obj] = Some post)
      (HminsF: Forall (FirstMPI msgs) rins)
      (HminsV: ValidMsgsIn sys rins)
      (Hprec: rule_precond rule post porq rins)
      (Htrs: rule_trs rule post porq rins = (nost, norq, routs))
      (HmoutsV: ValidMsgsOut sys routs)
      (Hmdisj: DisjList (idsOf rins) (idsOf routs)).

    Ltac disc_rule_custom ::=
      try disc_footprints_ok;
      try disc_messages_out;
      try disc_msg_case.

    Ltac inv_MsgOutsInv :=
      repeat
        match goal with
        | [H: MsgOutsInv _ _ _ _ |- _] => inv H
        end;
      repeat
        match goal with
        | [H: SubList [_] _ |- _] => apply SubList_singleton_In in H
        | [H: In _ nil |- _] => dest_in
        | [H: In _ [_] |- _] => dest_in
        | [H1: In _ ?eouts, H2: Forall _ ?eouts |- _] =>
          rewrite Forall_forall in H2;
          let oidx := fresh "oidx" in pose proof (H2 _ H1) as [oidx ?]
        | [H: RqDownMsgOutInv _ _ _ _ _ \/ RsUpMsgOutInv _ _ _ _ _ |- _] => destruct H
        | [H: RqDownMsgOutInv _ _ _ _ _ |- _] => red in H; dest
        | [H: RsUpMsgOutInv _ _ _ _ _ |- _] => red in H; dest
        | [H: RqUpMsgFrom _ _ |- _] => disc_rule_conds; solve_midx_false; fail
        | [H: RsDownMsgTo _ _ |- _] => disc_rule_conds; solve_midx_false; fail
        | [H: RqDownMsgTo _ _ |- _] => disc_rule_conds; solve_midx_false; fail
        | [H: RsUpMsgFrom _ _ |- _] => disc_rule_conds; solve_midx_false; fail
        end.

    Lemma step_msg_outs_ok_ImmDownRule:
      ImmDownRule dtr (obj_idx obj) rule ->
      MsgOutsInv (obj_idx obj :: oindsOf hst)
                 (st_orqs st0) (orqs +[obj_idx obj <- norq])
                 (removeL (id_dec msg_dec) eouts rins ++ routs).
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      disc_rule_conds.
      replace (orqs+[obj_idx obj <- norq]) with orqs by meq.
      inv_MsgOutsInv.

      unfold removeOnce.
      destruct (id_dec msg_dec _ _); [clear e; simpl|exfalso; auto].
      eapply MsgOutsRsDown.
      - red; eauto.
      - red; intros; dest_in; eauto.
        apply parent_not_in_subtree; [apply Hrrs|]; assumption.
      - disc_rule_conds.
        red; intros; dest_in; [exfalso; disc_rule_conds|].
        apply (DisjList_cons_inv idx_dec).
        + eapply H3; eauto.
        + intro Hx.
          apply subtreeIndsOf_child_SubList in H17; [|apply Hrrs].
          apply subtreeIndsOf_SubList in H12; [|apply Hrrs].
          apply H17, H12 in Hx.
          eapply parent_not_in_subtree; [apply Hrrs|..]; eauto.
      - disc_rule_conds.
        red; intros; dest_in; [simpl_locks|].
        apply H7; assumption.
      - red; intros; dest_in; [simpl_locks|].
        disc_rule_conds.
        elim H13; auto.
    Qed.

    Lemma step_msg_outs_ok_ImmUpRule:
      ImmUpRule dtr (obj_idx obj) rule ->
      MsgOutsInv (obj_idx obj :: oindsOf hst)
                   (st_orqs st0) (orqs +[obj_idx obj <- norq])
                   (removeL (id_dec msg_dec) eouts rins ++ routs).
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      disc_rule_conds.
      replace (orqs+[obj_idx obj <- norq]) with orqs by meq.
      inv_MsgOutsInv.

      pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H11).
      destruct H14 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      assert (In rqFrom (idsOf eouts))
        by (apply in_map_iff; exists (rqFrom, rqm); auto).
      pose proof (atomic_down_out_in_history
                    Hiorqs Hrrs Hatm Hrch Hsteps _ H11 H16 H15); clear H15.
      assert (Forall (fun eout => exists oidx, RqDownRsUpIdx oidx eout) eouts)
        by (eapply rqDown_rsUp_inv_msg, Forall_forall; eauto).

      eapply MsgOutsRqDownRsUp.
      - (** [RqDownRsUpDisj] *)
        eapply rqDownRsUpDisj_removeOnce_add_same; eauto.
        + left; red; eauto.
        + right; red; eauto.

      - (** Invariant for each message *)
        apply Forall_app.
        + (* For the others except (rqFrom, rqm) *)
          apply Forall_forall.
          intros [midx msg] ?.
          apply removeOnce_In_NoDup in H19;
            [|eapply rqDownRsUpDisj_NoDup in H2; [|eassumption];
              apply idsOf_NoDup; assumption]; dest.
          pose proof (H3 _ H20).
          destruct H21 as [oidx ?].
          destruct H21.
          * (* RqDown *)
            exists oidx; left.
            red in H21; dest.
            red; repeat ssplit; [assumption|..].
            { apply (DisjList_cons_inv idx_dec); [assumption|].
              eapply rqDown_no_rqDown
                with (rqdm:= (midx, msg)) (orqdm:= (rqFrom, rqm)); eauto.
              red; auto.
            }
            { red; intros; dest_in; [|eauto].
              exfalso.
              eapply steps_not_in_history_no_new_uplocks; eauto.
              intro Hx; eapply DisjList_In_2 in Hx; [|eapply H12].
              elim Hx; eapply rqEdgeUpFrom_subtreeIndsOf_self_in; [apply Hrrs|].
              congruence.
            }
          * (* RsUp *)
            exists oidx; right.
            red in H21; dest.
            red; repeat ssplit; [assumption|..].
            { red; simpl; intros.
              destruct H24; [subst|auto].
              split.
              { eapply steps_not_in_history_no_new_uplocks
                  with (st2:= {| st_oss := oss;
                                 st_orqs := orqs;
                                 st_msgs := msgs |}); eauto.
                eapply DisjList_In_1; [eassumption|].
                apply rqEdgeUpFrom_subtreeIndsOf_self_in; [apply Hrrs|congruence].
              }
              { red; mred. }
            }
            { red; intros; dest_in; [|eauto].
              exfalso.
              eapply steps_not_in_history_no_new_uplocks; eauto.
              intro Hx; eapply DisjList_In_2 in Hx; [|eapply H12].
              elim Hx; eapply rqEdgeUpFrom_subtreeIndsOf_self_in; [apply Hrrs|].
              congruence.
            }
        + (* For the new output *)
          repeat constructor.
          exists (obj_idx obj); right.
          red; repeat ssplit; [red; auto|..].
          * red; simpl; intros.
            destruct H19.
            { subst; split.
              { eapply steps_not_in_history_no_new_uplocks
                  with (st2:= {| st_oss := oss;
                                 st_orqs := orqs;
                                 st_msgs := msgs |}); eauto.
                eapply DisjList_In_1; [eassumption|].
                apply rqEdgeUpFrom_subtreeIndsOf_self_in; [apply Hrrs|congruence].
              }
              { simpl_locks. }
            }
            { specialize (H12 oidx); destruct H12; exfalso; auto. }
          * red; intros; dest_in; [|eauto].
            exfalso.
            eapply steps_not_in_history_no_new_uplocks; eauto.
            intro Hx; eapply DisjList_In_2 in Hx; [|eapply H12].
            elim Hx; eapply rqEdgeUpFrom_subtreeIndsOf_self_in; [apply Hrrs|].
            congruence.

      - (* [DownLocksCoverInv] *)
        red; simpl; intros.
        destruct H19; [subst; simpl_locks|].
        red; intros.
        red; simpl.
        apply (DisjList_cons_inv idx_dec); [eapply H5; eauto|].
        intro Hx.
        specialize (H5 _ _ H19 H20 H21).
        specialize (H5 _ _ _ H22 H23 H24 H25 H26).
        eapply DisjList_In_2 in H18; [|eapply H5].
        eapply inside_child_outside_parent_case in Hx;
          try eassumption; try apply Hrrs; subst.
        disc_rule_conds.
        pose proof (steps_object_in_system Hsteps _ H19).
        destruct H22 as [dobj [? ?]]; subst.
        good_locking_get dobj; mred.
        red in H21, H23.
        destruct (orqs@[obj_idx dobj]) as [dorq|]; simpl in *; auto.
        rewrite H21 in H23; dest.
        specialize (H24 _ H16).
        destruct H24 as [rdown [rsUp ?]]; dest.
        disc_rule_conds.
        destruct (in_dec idx_dec rsUp _); [auto|].
        red in H28; dest.
        eapply rqsQ_length_zero_False; eauto.

      - (** [DownLockRootInv] *)
        intros.
        assert (DownLockRoot (oindsOf hst) (st_orqs st0) orqs
                             roidx rrqid orcidx).
        { red in H19; dest.
          destruct H19; subst; [exfalso; simpl_locks|].
          red; repeat ssplit; assumption.
        }
        specialize (H8 _ _ _ H20); clear H19 H20.
        specialize (H3 _ Hosub).
        destruct H3 as [oidx ?].
        destruct H3; [|destruct H3; disc_rule_conds].
        destruct H3.
        assert (oidx = obj_idx obj) by disc_rule_conds; subst.
        red in H8; dest.
        pose proof H8.
        red in H23; rewrite Forall_forall in H23.
        specialize (H23 _ Hosub).
        red in H23; dest.
        specialize (H23 _ _ H3 H16); dest.
        disc_rule_conds.

        repeat split.
        + (* [OutsInRoot] *)
          apply Forall_app.
          * apply forall_removeOnce; assumption.
          * constructor; [|constructor].
            split; [red; intros; disc_rule_conds|].
            red; intros; split; disc_rule_conds.
        + destruct orcidx as [rcidx|]; [dest|auto].
          repeat ssplit.
          * (* [DisjExceptUpLocked] *)
            disc_rule_conds.
            apply disjExceptUpLocked_history_add; auto.
          * (* [UpLockCoverInv] *)
            red; intros; dest_in; [exfalso; auto|].
            apply (DisjList_cons_inv idx_dec); [eapply H26; eauto|].
            intro Hx; elim H25.
            apply subtreeIndsOf_child_SubList in H32; [|apply Hrrs].
            apply H32 in Hx.
            apply subtreeIndsOf_SubList in H28; [|apply Hrrs].
            apply H28; assumption.
          * (* [UpLockedBound] *)
            red; intros; dest_in.
            { exfalso; eapply steps_not_in_history_no_new_uplocks; eauto. }
            { apply H27; auto. }
        + (* [NoDownLockOutside] *)
          red; intros; dest_in; [|eauto].
          elim H27; eapply inside_child_in; [apply Hrrs|..]; eassumption.
    Qed.

    Lemma step_msg_outs_ok_RsDownRqDownRule:
      RsDownRqDownRule dtr sys (obj_idx obj) rule ->
      MsgOutsInv (obj_idx obj :: oindsOf hst)
                   st0.(st_orqs) (orqs +[obj_idx obj <- norq])
                                  (removeL (id_dec msg_dec) eouts rins ++ routs).
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      good_footprint_get (obj_idx obj).
      disc_rule_conds.
      inv_MsgOutsInv.
      unfold removeOnce in *.
      destruct (id_dec msg_dec _ _); [clear e; simpl|exfalso; auto].
      simpl in *.
      disc_rule_conds.

      assert (UpLockedBound (obj_idx obj :: oindsOf hst) (st_orqs st0)
                            (orqs +[obj_idx obj <- ((porq) -[ upRq]) +[ downRq <- rqi0]])
                            (obj_idx upCObj)) as Hulb.
      { eapply upLockedBound_child; eauto; [|congruence|mred].
        intros.
        eapply atomic_separation_ok in H20; eauto; try apply Hiorqs.
        destruct H20; [|assumption].
        exfalso; destruct H20 as [ccidx [? ?]].
        pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H5).
        destruct H26 as [rqUp [rrsUp [pidx ?]]]; dest.
        disc_rule_conds.
        pose proof Hatm.
        eapply atomic_down_out_in_history with (down:= rsFrom0) in H26;
          eauto; try apply Hiorqs; [|left; reflexivity].
        apply H22 in H26.
        eapply parent_parent_in_False with (oidx2:= obj_idx obj);
          try apply Hrrs; eassumption.
      }

      eapply MsgOutsRqDownRsUp.
      - (** [RqDownRsUpDisj] *)
        eapply rqDownRsUpDisj_down_children; [apply HmoutsV|eassumption].

      - (** Invariant for each message *)
        apply Forall_forall.
        intros [rrqTo rqm] ?.
        assert (In rrqTo (idsOf routs))
          by (apply in_map_iff; exists (rrqTo, rqm); auto).
        eapply RqRsDownMatch_rq_rs in H18; [|eassumption].
        destruct H18 as [cidx [rsUp ?]]; dest.
        rewrite Forall_forall in H14.
        pose proof (H14 _ H20); simpl in H30.
        disc_rule_conds.
        exists cidx; left.

        red; repeat ssplit; [red; auto|..].
        + red; simpl.
          apply (DisjList_cons_inv idx_dec);
            [|apply parent_not_in_subtree; [apply Hrrs|auto]].
          destruct (in_dec idx_dec (obj_idx obj) (oindsOf hst)).
          * eapply H15; eauto.
            { eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption]. }
            { intro Hx; subst.
              disc_rule_conds; auto.
            }
          * eapply atomic_separation_ok in n; eauto; try apply Hiorqs.
            destruct n.
            1: {
              exfalso; destruct H31 as [rcidx [? ?]].
              pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H5).
              destruct H33 as [rqUp [rrsUp [pidx ?]]]; dest.
              disc_rule_conds.
              pose proof Hatm.
              eapply atomic_down_out_in_history with (down:= rsFrom0) in H33;
                eauto; try apply Hiorqs; [|left; reflexivity].
              apply H32 in H33.
              eapply parent_parent_in_False with (oidx2:= obj_idx obj);
                try apply Hrrs; eassumption.
            }
            eapply DisjList_comm, DisjList_SubList.
            { eapply subtreeIndsOf_child_SubList; [apply Hrrs|eassumption]. }
            { apply DisjList_comm; assumption. }

        + eapply upLockedBound_OutsideUpLocked; eauto.
          eapply subtreeIndsOf_other_child_not_in; [apply Hrrs|..]; eauto.

      - (** [DownLocksCoverInv] *)
        red; intros.
        icase oidx.
        2: {
          exfalso.
          simpl_locks.
          specialize (H13 _ H20 H22).
          specialize (H19 _ H20 H13).
          simpl_locks.
          destruct (orqs@[oidx]); simpl in *; [congruence|exfalso; auto].
        }

        simpl_locks.
        clear H22.
        destruct (in_dec idx_dec (obj_idx obj) (oindsOf hst)).
        + red; intros.
          assert (In (obj_idx obj) (subtreeIndsOf dtr (obj_idx obj))).
          { eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption]. }
          specialize (H15 (obj_idx obj) H30 i _ _ Hporq H16); clear H30.
          apply (DisjList_cons_inv idx_dec).
          * eapply H15; try eassumption; congruence.
          * eapply parent_not_in_subtree; [apply Hrrs|assumption].
        + eapply atomic_separation_ok in n; eauto; try apply Hiorqs.
          destruct n.
          1: {
            exfalso; destruct H22 as [ccidx [? ?]].
            pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H5).
            destruct H27 as [rqUp [rrsUp [pidx ?]]]; dest.
            disc_rule_conds.
            pose proof Hatm.
            eapply atomic_down_out_in_history with (down:= rsFrom0) in H27;
              eauto; try apply Hiorqs; [|left; reflexivity].
            apply H26 in H27.
            eapply parent_parent_in_False with (oidx2:= obj_idx obj);
              try apply Hrrs; eassumption.
          }

          red; intros.
          apply (DisjList_cons_inv idx_dec).
          * eapply DisjList_comm, DisjList_SubList.
            { eapply subtreeIndsOf_child_SubList; [apply Hrrs|eassumption]. }
            { apply DisjList_comm; assumption. }
          * eapply parent_not_in_subtree; [apply Hrrs|assumption].

      - (** [DownLockRootInv] *)
        intros; red in H20; dest.
        icase roidx.
        2: {
          exfalso.
          destruct (in_dec idx_dec roidx (subtreeIndsOf dtr (obj_idx obj))).
          { eapply H13; eauto; simpl_locks. }
          { specialize (H19 _ H20 n0); simpl_locks.
            destruct (orqs@[roidx]); simpl in *; congruence.
          }
        }

        simpl_locks.
        destruct orcidx as [rcidx|]; [dest|congruence].
        clear H22.
        red; repeat split.
        + (* [OutsInRoot] *)
          apply Forall_forall.
          intros [rrqTo rqm] ?.
          assert (In rrqTo (idsOf routs))
            by (apply in_map_iff; exists (rrqTo, rqm); auto).
          eapply RqRsDownMatch_rq_rs in H18; [|eassumption].
          destruct H18 as [cidx [rsUp ?]]; dest.
          rewrite Forall_forall in H14.
          pose proof (H14 _ H22); simpl in H14.
          split.
          * red; intros; disc_rule_conds.
            split.
            { eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption]. }
            { eapply subtreeIndsOf_other_child_not_in; [apply Hrrs|..]; eauto. }
          * red; intros; disc_rule_conds.

        + (* [DisjExceptUpLocked] *)
          eapply disjExceptUpLocked_child; eauto.
        + (* [UpLockCoverInv] *)
          eapply upLockCoverInv_child; eauto.
        + (* [UpLockedBound] *)
          rewrite H23 in H27; disc_rule_conds.
        + (* [NoDownLockOutside] *)
          red; intros.
          icase oidx.
          * elim H28; eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption].
          * simpl_locks; eapply H19; eauto.
    Qed.

    Lemma step_msg_outs_ok_RqFwdRule:
      RqFwdRule dtr sys (obj_idx obj) rule ->
      MsgOutsInv (obj_idx obj :: oindsOf hst)
                   (st_orqs st0) (orqs +[obj_idx obj <- norq])
                   (removeL (id_dec msg_dec) eouts rins ++ routs).
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      disc_rule_conds.

      - (** [RqUpUp] *)
        inv_MsgOutsInv.
        unfold removeOnce.
        destruct (id_dec msg_dec _ _); [clear e; simpl|exfalso; auto].
        disc_rule_conds.
        eapply MsgOutsRqUp; [red; eauto|..].
        + (* [UpLockCoverInv] *)
          red; intros.
          icase oidx0.
          * mred; apply (DisjList_cons_inv idx_dec).
            { eapply DisjList_SubList; [eassumption|].
              eapply subtreeIndsOf_child_disj; [apply Hrrs|..]; try eassumption.
              intro Hx; subst; disc_rule_conds; auto.
            }
            { eapply parent_not_in_subtree; [apply Hrrs|assumption]. }
          * mred; apply (DisjList_cons_inv idx_dec).
            { eapply H11; eauto. }
            { apply subtreeIndsOf_child_SubList in H23; [|apply Hrrs].
              intro Hx; apply H23 in Hx.
              elim n; eapply subtreeIndsOf_In_each_other_eq;
                [apply Hrrs|..]; eassumption.
            }
        + (* [UpLockedBound] *)
          red; intros.
          icase oidx0.
          * eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption].
          * simpl_locks.
            specialize (H14 _ H19 H20).
            apply subtreeIndsOf_child_SubList in H2; [|apply Hrrs].
            apply H2; assumption.
        + (* History coverage *)
          apply SubList_cons.
          * eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption].
          * apply subtreeIndsOf_child_SubList in H2; [|apply Hrrs].
            eapply SubList_trans; eauto.

        + (* [UpLockedTotal] *)
          red; intros.
          icase oidx0.
          * eapply upLockedNew_index_eq_2 with (orqs2:= orqs).
            { pose proof Hsteps.
              eapply steps_locks_unaffected with (oidx0:= obj_idx obj) in H20.
              { assumption. }
              { intro Hx; apply H17 in Hx.
                eapply parent_not_in_subtree; [apply Hrrs|..]; eassumption.
              }
            }
            { simpl_locks; split; [discriminate|reflexivity]. }
          * simpl_locks; apply H18; assumption.

      - (** [RqUpDown] *)
        inv_MsgOutsInv.
        unfold removeOnce in *.
        destruct (id_dec msg_dec _ _); [clear e; simpl|exfalso; auto].
        disc_rule_conds.

        eapply MsgOutsRqDownRsUp.
        + (** [RqDownRsUpDisj] *)
          eapply rqDownRsUpDisj_down_children; [apply HmoutsV|eassumption].

        + (** Invariant for each message *)
          apply Forall_forall.
          intros [rqTo rqm] ?.
          assert (In rqTo (idsOf routs))
            by (apply in_map_iff; exists (rqTo, rqm); auto).
          eapply RqRsDownMatch_rq_rs in H9; [|eassumption].
          destruct H9 as [cidx [rsUp ?]]; dest.
          rewrite Forall_forall in H20.
          pose proof (H20 _ H18); simpl in H25.
          exists cidx; left.
          red; repeat ssplit; [red; eauto|..].
          { apply (DisjList_cons_inv idx_dec);
              [|apply parent_not_in_subtree; [apply Hrrs|auto]].
            eapply DisjList_SubList; [eassumption|].
            eapply subtreeIndsOf_child_disj; [apply Hrrs|..]; eauto.
          }
          { red; intros.
            icase uidx.
            { exfalso.
              eapply steps_not_in_history_no_new_uplocks
                with (oidx:= obj_idx obj); eauto.
              { intro Hx; apply H15 in Hx.
                eapply parent_not_in_subtree
                  with (oidx:= obj_idx upCObj); [apply Hrrs|..]; eassumption.
              }
              { simpl; simpl_locks; assumption. }
            }
            { eapply upLockedBound_OutsideUpLocked; eauto.
              intro Hx.
              eapply subtreeIndsOf_other_child_not_in
                with (cidx1:= cidx) (cidx2:= obj_idx upCObj);
                [apply Hrrs|..]; eassumption.
            }
          }

        + (** [DownLocksCoverInv] *)
          red; intros.
          icase oidx.
          * clear H18 H19.
            simpl_locks.
            red; intros.
            apply (DisjList_cons_inv idx_dec).
            { eapply DisjList_SubList; [eassumption|].
              eapply subtreeIndsOf_child_disj; [apply Hrrs|..]; eauto.
              intro Hx; subst; disc_rule_conds; auto.
            }
            { eapply parent_not_in_subtree; [apply Hrrs|assumption]. }
          * specialize (H17 _ H18).
            simpl_locks.

        + (** [DownLockRootInv] *)
          intros; red in H18; dest.
          icase roidx; [|exfalso; specialize (H17 _ H18); simpl_locks].
          clear H18.
          simpl_locks.
          destruct orcidx as [rcidx|]; [dest|congruence].
          disc_rule_conds.
          red; repeat split.
          * (* [OutsInRoot] *)
            apply Forall_forall.
            intros [rqTo rqm] ?.
            assert (In rqTo (idsOf routs))
              by (apply in_map_iff; exists (rqTo, rqm); auto).
            eapply RqRsDownMatch_rq_rs in H9; [|eassumption].
            destruct H9 as [cidx [rsUp ?]]; dest.
            rewrite Forall_forall in H20.
            pose proof (H20 _ H18); simpl in H26.
            split.
            { red; intros; disc_rule_conds.
              split.
              { eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption]. }
              { eapply subtreeIndsOf_other_child_not_in; [apply Hrrs|..]; eauto. }
            }
            { red; intros; disc_rule_conds. }

          * (* [DisjExceptUpLocked] *)
            red; intros.
            icase oidx.
            { eapply parent_not_in_subtree; [apply Hrrs|eassumption]. }
            { specialize (H17 _ H18); simpl_locks. }

          * (* [UpLockCoverInv] *)
            red; intros.
            icase oidx.
            { exfalso.
              eapply parent_not_in_subtree with (oidx:= obj_idx upCObj);
                [apply Hrrs|..]; eauto.
            }
            { mred; apply (DisjList_cons_inv idx_dec).
              { eapply H11; eauto. }
              { intro Hx.
                eapply subtreeIndsOf_child_SubList in H24; [|apply Hrrs].
                apply subtreeIndsOf_SubList in H18; [|apply Hrrs].
                apply H24, H18 in Hx.
                eapply parent_not_in_subtree; [apply Hrrs|..]; eauto.
              }
            }

          * (* [UpLockedBound] *)
            red; intros.
            icase oidx; [simpl_locks; exfalso; auto|].
            apply H15; auto.

          * (* [NoDownLockOutside] *)
            red; intros; dest_in.
            { elim H21.
              eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption].
            }
            { elim H21; apply H15 in H22.
              eapply subtreeIndsOf_child_SubList; [apply Hrrs|..]; eassumption.
            }

      - (** [RqDownDown] *)
        inv_MsgOutsInv.
        pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H2).
        destruct H18 as [rqUp [rsUp [pidx ?]]]; dest.
        disc_rule_conds.
        assert (In rqFrom (idsOf eouts))
          by (apply in_map_iff; exists (rqFrom, rqfm); auto).
        pose proof (atomic_down_out_in_history
                      Hiorqs Hrrs Hatm Hrch Hsteps _ H2 H21 H19); clear H19.

        eapply MsgOutsRqDownRsUp.
        + (** [RqDownRsUpDisj] *)
          eapply rqDownRsUpDisj_parent_down_children; eauto.
          * eapply rqDown_rsUp_inv_msg, Forall_forall; eauto.
          * left; red; auto.
          * apply HmoutsV.

        + (** Invariant for each message *)
          apply Forall_app.
          * apply Forall_forall.
            intros [midx msg] ?.
            apply removeOnce_In_NoDup in H19;
              [|apply idsOf_NoDup, rqDownRsUpDisj_NoDup; auto;
                eapply rqDown_rsUp_inv_msg, Forall_forall; eauto]; dest.
            pose proof (H7 _ H23).
            destruct H24 as [oidx ?].

            assert (forall oidx,
                       OutsideUpLocked (oindsOf hst) (st_orqs st0) orqs oidx ->
                       OutsideUpLocked
                         (obj_idx obj :: oindsOf hst)
                         (st_orqs st0)
                         (orqs +[obj_idx obj <- (porq +[downRq <- rqi])]) oidx)
              as Houl.
            { intros; red; intros.
              icase uidx.
              { exfalso.
                eapply steps_not_in_history_no_new_uplocks
                  with (oidx:= obj_idx obj); eauto.
                { intro Hx; eapply DisjList_In_2 in Hx; [|apply H15].
                  elim Hx; eapply rqEdgeUpFrom_subtreeIndsOf_self_in; [apply Hrrs|].
                  congruence.
                }
                { simpl; simpl_locks; assumption. }
              }
              { apply H26; auto.
                simpl_locks.
              }
            }

            destruct H24.
            { (* RqDown *)
              exists oidx; left.
              red in H24; dest.
              red; repeat ssplit; [assumption|..].
              { red; simpl.
                apply (DisjList_cons_inv idx_dec); [assumption|].
                eapply rqDown_no_rqDown
                  with (eouts:= eouts)
                       (rqdm:= (midx, msg))
                       (orqdm:= (rqFrom, rqfm)); eauto.
                { eapply rqDown_rsUp_inv_msg, Forall_forall; eauto. }
                { red; auto. }
              }
              { apply Houl; assumption. }
            }
            { (* RsUp *)
              exists oidx; right.
              red in H24; dest.
              red; repeat ssplit; [assumption|..].
              { red; intros.
                icase oidx0.
                { subst; exfalso.
                  eapply rsUp_no_rqDown
                    with (eouts:= eouts)
                         (rsum:= (midx, msg))
                         (orqdm:= (rqFrom, rqfm)); eauto.
                  { eapply rqDown_rsUp_inv_msg, Forall_forall; eauto. }
                  { red; auto. }
                }
                { specialize (H26 _ H29 H30); dest.
                  split; simpl_locks.
                }
              }
              { apply Houl; assumption. }
            }

          * apply Forall_forall.
            intros [rqTo rqm] ?.
            assert (In rqTo (idsOf routs))
              by (apply in_map_iff; exists (rqTo, rqm); auto).
            eapply RqRsDownMatch_rq_rs in H4; [|eassumption].
            destruct H4 as [cidx [rrsUp ?]]; dest.
            rewrite Forall_forall in H20.
            pose proof (H20 _ H19); simpl in H28.
            exists cidx; left.
            red; repeat ssplit; [red; auto|..].
            { apply (DisjList_cons_inv idx_dec).
              { apply DisjList_comm in H15.
                eapply DisjList_comm, DisjList_SubList;
                  [|eassumption].
                eapply subtreeIndsOf_child_SubList;
                  [apply Hrrs|assumption].
              }
              { apply parent_not_in_subtree; [apply Hrrs|auto]. }
            }
            { red; intros.
              icase uidx.
              { exfalso.
                eapply steps_not_in_history_no_new_uplocks
                  with (oidx:= obj_idx obj); eauto.
                { intro Hx; eapply DisjList_In_2 in Hx; [|eassumption].
                  elim Hx; eapply rqEdgeUpFrom_subtreeIndsOf_self_in; [apply Hrrs|].
                  congruence.
                }
                { simpl; simpl_locks; assumption. }
              }
              { simpl_locks.
                specialize (H17 _ H31 H32).
                intro Hx; elim H17.
                eapply inside_parent_in; [apply Hrrs|..]; try eassumption.
                intro; subst.
                eapply DisjList_In_2 in H31; [|eassumption].
                elim H31; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
              }
            }

        + (** [DownLocksCoverInv] *)
          red; intros; icase oidx.
          { clear H19 H23.
            simpl_locks.
            red; intros.
            apply (DisjList_cons_inv idx_dec).
            { eapply subtreeIndsOf_child_SubList in H19; [|apply Hrrs].
              eapply DisjList_comm, DisjList_SubList; [eassumption|].
              apply DisjList_comm; assumption.
            }
            { eapply parent_not_in_subtree; [apply Hrrs|assumption]. }
          }
          { red; intros.
            simpl_locks.
            specialize (H11 _ _ H19 H23 H24 _ _ _ H26 H28 H29 H30 H31).
            apply (DisjList_cons_inv idx_dec); [assumption|].
            eapply DisjList_In_2 in H22; [|eapply H11].
            intro Hx; elim H22.
            eapply inside_parent_in; [apply Hrrs|..]; try eassumption.
            intro; subst; disc_rule_conds.
            eapply steps_object_in_system in H19; [|eassumption].
            destruct H19 as [pobj [? ?]]; subst.
            good_locking_get pobj.
            eapply downLockInvORq_down_rqsQ_length_one_locked in H26;
              try eassumption;
              [|eapply rqsQ_length_ge_one;
                [eassumption|apply FirstMP_InMP; assumption]].
            destruct H26 as [prqid ?]; dest.
            disc_rule_conds.
            destruct (orqs@[obj_idx pobj]) as [pporq|] eqn:Horq; simpl in *; auto.
            rewrite H24 in H26; inv H26; auto.
          }

        + (** [DownLockRootInv] *)
          intros.
          destruct (idx_dec roidx (obj_idx obj)); subst.
          1: { red in H19; dest; simpl_locks.
               destruct orcidx as [rcidx|]; [dest|congruence].
               rewrite H27 in H26; solve_midx_false.
          }
          assert (DownLockRoot (oindsOf hst) (st_orqs st0) orqs roidx rrqid orcidx).
          { red in H19; dest.
            destruct H19; [exfalso; auto|].
            red; repeat ssplit; try assumption.
            { intro Hx; elim H23.
              eapply upLockedNew_index_eq_1 with (orqs2:= orqs); [mred|assumption].
            }
            { simpl_locks. }
          }
          specialize (H13 _ _ _ H23); clear H23.
          red in H13; dest.
          pose proof H13.
          red in H26; rewrite Forall_forall in H26.
          specialize (H26 _ Hosub).
          red in H26; dest; clear H28.
          assert (RqDownMsgTo (obj_idx obj) (rqFrom, rqfm)) by (red; auto).
          specialize (H26 _ _ H28 H21); dest.

          red; repeat ssplit.
          * (* [OutsInRoot] *)
            apply Forall_app.
            { apply forall_removeOnce; assumption. }
            { apply Forall_forall; intros [rqTo rqm] ?.
              assert (In rqTo (idsOf routs))
                by (apply in_map_iff; exists (rqTo, rqm); auto).
              eapply RqRsDownMatch_rq_rs in H4; [|eassumption].
              destruct H4 as [cidx [rrsUp ?]]; dest.
              red; split; [|red; intros; disc_rule_conds; solve_midx_false].
              red; intros; disc_rule_conds; split.
              { eapply inside_child_in; [apply Hrrs|..]; eauto. }
              { destruct orcidx as [rcidx|]; [simpl in *; dest|auto].
                eapply outside_child_in in H29; [|apply Hrrs|eassumption].
                destruct H29; auto; subst.
                red in H19; dest.
                disc_rule_conds.
              }
            }

          * destruct orcidx as [rcidx|]; [simpl in *; dest|auto].
            repeat ssplit.
            { (* [DisjExceptUpLocked] *)
              red; intros.
              icase oidx; [assumption|].
              eapply H23; eauto.
              intro Hx; elim H33.
              eapply upLockedNew_index_eq_1; [mred|eassumption].
            }
            { red; intros.
              icase oidx; [exfalso; auto|].
              mred; apply (DisjList_cons_inv idx_dec).
              { eapply H30; eauto. }
              { intro Hx.
                eapply subtreeIndsOf_child_SubList in H36; [|apply Hrrs].
                eapply subtreeIndsOf_SubList in H32; [|apply Hrrs].
                apply H36, H32 in Hx; auto.
              }
            }
            { (* [UpLockedBound] *)
              red; intros; icase oidx.
              { exfalso.
                eapply steps_not_in_history_no_new_uplocks
                  with (oidx:= obj_idx obj); eauto.
                intro Hx; eapply DisjList_In_2 in Hx; [|eassumption].
                elim Hx; apply rqEdgeUpFrom_subtreeIndsOf_self_in; [apply Hrrs|..].
                { congruence. }
                { simpl; simpl_locks; assumption. }
              }
              { simpl_locks.
                apply H31; assumption.
              }
            }

          * (* [NoDownLockOutside] *)
            red; intros; icase oidx.
            { elim H31; eapply inside_child_in; [apply Hrrs|..]; eassumption. }
            { simpl_locks; eapply H24; eauto. }
    Qed.

    Lemma step_msg_outs_ok_RsBackRule:
      RsBackRule rule ->
      MsgOutsInv (obj_idx obj :: oindsOf hst)
                   (st_orqs st0) (orqs +[obj_idx obj <- norq])
                   (removeL (id_dec msg_dec) eouts rins ++ routs).
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      good_footprint_get (obj_idx obj).
      disc_rule_conds.

      - (** [RsDownDown] *)
        inv_MsgOutsInv.
        rewrite removeOnce_nil; simpl.
        disc_rule_conds.
        assert (forall ccidx,
                   parentIdxOf dtr ccidx = Some (obj_idx obj) ->
                   SubList (oindsOf hst) (subtreeIndsOf dtr ccidx) ->
                   False) as Hcf.
        { intros.
          pose proof (edgeDownTo_Some (proj1 (proj2 H)) _ H7).
          destruct H22 as [rqUp [rrsUp [pidx ?]]]; dest.
          disc_rule_conds.
          pose proof Hatm.
          eapply atomic_down_out_in_history with (down:= rsFrom) in H22;
            eauto; try apply Hiorqs; [|left; reflexivity].
          apply H21 in H22.
          eapply parent_parent_in_False with (oidx2:= obj_idx obj);
            try apply Hrrs; eassumption.
        }

        eapply MsgOutsRsDown; [red; eauto|..].
        + eapply disjExceptUpLocked_child; eauto.
        + eapply upLockCoverInv_child; eauto.
        + eapply upLockedBound_child; eauto; [|congruence|mred].
          intros.
          eapply atomic_separation_ok in H20; eauto; try apply Hiorqs.
          destruct H20; [|assumption].
          exfalso; destruct H20 as [ccidx [? ?]].
          eapply Hcf; eauto.
        + destruct (in_dec idx_dec (obj_idx obj) (oindsOf hst)).
          * eapply noDownLockOutside_child_in_1; eauto; mred.
          * eapply atomic_separation_ok in n; eauto; try apply Hiorqs.
            destruct n.
            { exfalso; destruct H20 as [rcidx [? ?]].
              eapply Hcf; eauto.
            }
            { eapply noDownLockOutside_child_out; eauto; mred. }

      - (** [RsDownDown-silent] *)
        inv_MsgOutsInv.
        rewrite removeOnce_nil; simpl.
        constructor.

      - (** [RsUpDown] *)
        inv_MsgOutsInv.
        1: { exfalso; apply SubList_nil_inv in Hosub; auto. }
        1: {
          exfalso.
          eapply SubList_singleton_NoDup in Hosub;
            [|apply idsOf_NoDup, HminsV].
          destruct Hosub; [exfalso; auto|subst].
          eapply RqRsDownMatch_rs_rq in H11; [|rewrite <-H17; left; reflexivity].
          destruct H11 as [cidx [down ?]]; dest.
          disc_rule_conds.
        }
        1: {
          exfalso.
          eapply SubList_singleton_NoDup in Hosub;
            [|apply idsOf_NoDup, HminsV].
          destruct Hosub; [exfalso; auto|subst].
          eapply RqRsDownMatch_rs_rq in H11; [|rewrite <-H17; left; reflexivity].
          destruct H11 as [cidx [down ?]]; dest.
          disc_rule_conds.
          solve_midx_false.
        }

        destruct (in_dec idx_dec (obj_idx obj) (oindsOf hst)).
        + (** If the history has visited the root *)
          assert (~ UpLockedNew (st_orqs st0) orqs (obj_idx obj)).
          { assert (exists rsUp rsum, In (rsUp, rsum) rins).
            { destruct rins as [|[rsUp rsum] ?]; [exfalso; auto|].
              do 2 eexists; left; reflexivity.
            }
            destruct H18 as [rsUp [rsum ?]].
            pose proof H18.
            apply in_map with (f:= idOf) in H19; simpl in H19.
            eapply RqRsDownMatch_rs_rq in H11; [|rewrite <-H17; eassumption].
            destruct H11 as [cidx [down ?]]; dest.
            apply Hosub in H18.
            rewrite Forall_forall in H13; specialize (H13 _ H18).
            destruct H13 as [oidx ?].
            destruct H13; [destruct H13; disc_rule_conds; solve_midx_false|].
            red in H13; dest; disc_rule_conds.
            intro Hx.
            specialize (H25 _ i Hx).
            elim H25; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
          }
          assert (DownLocked orqs (obj_idx obj) rqi) by simpl_locks.
          assert (DownLockRoot (oindsOf hst) (st_orqs st0) orqs
                               (obj_idx obj) rqi (Some (obj_idx upCObj))).
          { red; repeat ssplit; try eassumption; congruence. }
          specialize (H16 _ _ _ H20).
          red in H16; dest.
          specialize (H15 _ _ i H18 H19).
          assert (SubList eouts rins).
          { eapply rsUp_outs_case_back; eauto.
            { apply HminsV. }
            { eapply rqDown_rsUp_inv_msg; eauto. }
          }
          clear H20.

          rewrite SubList_NoDup_removeL_nil;
            [|assumption
             |apply idsOf_NoDup, rqDownRsUpDisj_NoDup; auto;
              eapply rqDown_rsUp_inv_msg; eauto].
          simpl; clear H25.

          eapply MsgOutsRsDown; [red; eauto|..].
          * red; intros; icase oidx.
            { eapply parent_not_in_subtree; [apply Hrrs|eassumption]. }
            { eapply H21; eauto; simpl_locks. }
          * red; intros; icase oidx.
            { exfalso; eapply parent_not_in_subtree with (oidx:= obj_idx upCObj);
                [apply Hrrs|..]; eassumption.
            }
            { mred; apply (DisjList_cons_inv idx_dec).
              { eapply H23; eauto. }
              { apply subtreeIndsOf_child_SubList in H28; [|apply Hrrs].
                apply subtreeIndsOf_SubList in H20; [|apply Hrrs].
                intro Hx; apply H28, H20 in Hx.
                eapply parent_not_in_subtree with (oidx:= obj_idx upCObj);
                  [apply Hrrs|..]; eassumption.
              }
            }
          * red; intros; icase oidx.
            { exfalso; simpl_locks. }
            { simpl_locks; apply H24; assumption. }
          * eapply noDownLockOutside_child_in; eauto; [|mred].
            intros.
            pose proof (parentIdxOf_Some (proj1 (proj2 H)) _ H20).
            destruct H27 as [orqUp [orsUp [down ?]]]; dest.
            disc_rule_conds.
            specialize (H15 _ _ _ H20 H28 H25).
            destruct (in_dec idx_dec orsUp (map fst (rqi_rss rqi)));
              [left|right; apply H15; [auto|congruence]].
            eapply RqRsDownMatch_rs_rq in H11; [|eassumption].
            destruct H11 as [cidx [odown ?]]; dest.
            disc_rule_conds.
            rewrite <-H17 in i0.
            apply in_map_iff in i0.
            destruct i0 as [[orsUp' orsm] [? ?]]; simpl in *; subst.
            apply Hosub in H30.
            rewrite Forall_forall in H13; specialize (H13 _ H30).
            destruct H13 as [oidx ?].
            destruct H13; [destruct H13; disc_rule_conds; solve_midx_false|].
            red in H13; dest; disc_rule_conds.

        + (** If the history never visited the root *)
          assert (exists rsFrom rsfm, In (rsFrom, rsfm) rins).
          { destruct rins as [|[rsFrom rsfm] ?]; [exfalso; auto|].
            do 2 eexists; left; reflexivity.
          }
          destruct H18 as [rsFrom [rsfm ?]].
          rewrite Forall_forall in H8.
          specialize (H8 _ H18); simpl in H8.
          assert (In rsFrom (idsOf rins))
            by (apply in_map with (f:= idOf) in H18; assumption).
          eapply RqRsDownMatch_rs_rq in H11; [|rewrite <-H17; eassumption]; clear H19.
          destruct H11 as [ccidx [down ?]]; dest.
          eapply Hosub in H18.
          assert (In rsFrom (idsOf eouts))
            by (apply in_map with (f:= idOf) in H18; assumption).
          pose proof (atomic_rsUp_out_in_history
                        Hiorqs Hrrs Hatm Hrch Hsteps _ H21 H23); clear H23.

          eapply atomic_separation_ok in n; eauto; try apply Hiorqs.
          destruct n.
          2: {
            exfalso.
            eapply DisjList_In_2 in H23; [|eassumption].
            elim H23; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
          }
          destruct H23 as [cidx [? ?]].
          destruct (idx_dec cidx ccidx); subst.
          2: {
            apply H25 in H24.
            exfalso.
            eapply subtreeIndsOf_other_child_not_in
              with (cidx1:= ccidx) (cidx2:= cidx) (pidx:= obj_idx obj);
              try apply Hrrs; eauto.
          }

          assert (RsUpMsgOutInv (oindsOf hst) (st_orqs st0) orqs ccidx (rsFrom, rsfm)).
          { rewrite Forall_forall in H13.
            specialize (H13 _ H18); destruct H13 as [oidx ?].
            destruct H13; [destruct H13; disc_rule_conds|].
            destruct H13; disc_rule_conds.
            split; [red; auto|assumption].
          }
          assert (eouts = [(rsFrom, rsfm)]); subst.
          { eapply rsUp_outs_case_isolated; eauto.
            eapply rqDown_rsUp_inv_msg; eauto.
          }

          destruct HminsV.
          eapply SubList_singleton_NoDup in Hosub;
            [|apply idsOf_NoDup, HminsV].
          destruct Hosub; [exfalso; auto|subst].
          rewrite removeL_nil in *; simpl in *.
          red in H26; dest.

          eapply MsgOutsRsDown; [red; eauto|..].
          * red; intros; icase oidx.
            { eapply parent_not_in_subtree; [apply Hrrs|eassumption]. }
            { eapply H25 in H31.
              eapply DisjList_In_2; [|eapply H31].
              eapply subtreeIndsOf_child_disj; [apply Hrrs|..]; eassumption.
            }
          * red; intros; icase oidx.
            { exfalso; eapply parent_not_in_subtree with (oidx:= obj_idx upCObj);
                [apply Hrrs|..]; eassumption.
            }
            { apply subtreeIndsOf_child_SubList in H35; [|apply Hrrs].
              apply subtreeIndsOf_SubList in H31; [|apply Hrrs].
              apply (DisjList_cons_inv idx_dec).
              { eapply DisjList_comm, DisjList_SubList.
                { eapply SubList_trans; eassumption. }
                { eapply DisjList_comm, DisjList_SubList; [eassumption|].
                  eapply subtreeIndsOf_child_disj; [apply Hrrs|..]; eassumption.
                }
              }
              { intro Hx; apply H35, H31 in Hx.
                eapply parent_not_in_subtree with (oidx:= obj_idx upCObj);
                  [apply Hrrs|..]; eassumption.
              }
            }
          * red; intros; exfalso.
            icase oidx.
            { eapply steps_not_in_history_no_new_uplocks
                with (oidx:= obj_idx obj); eauto.
              { intro Hx; apply H25 in Hx.
                eapply parent_not_in_subtree; [apply Hrrs|..]; eassumption.
              }
              { simpl; simpl_locks; assumption. }
            }
            { specialize (H29 _ H31 (H25 _ H31)); dest.
              simpl_locks.
            }
          * red; intros; icase oidx.
            { simpl_locks. }
            { simpl_locks; eapply H29; eauto. }

      - (** [RsUpUp] *)
        inv_MsgOutsInv.
        1: { exfalso; apply SubList_nil_inv in Hosub; auto. }
        1: {
          exfalso.
          eapply SubList_singleton_NoDup in Hosub;
            [|apply idsOf_NoDup, HminsV].
          destruct Hosub; [exfalso; auto|subst].
          eapply RqRsDownMatch_rs_rq in H6; [|rewrite <-H17; left; reflexivity].
          destruct H6 as [cidx [down ?]]; dest.
          disc_rule_conds.
        }
        1: {
          exfalso.
          eapply SubList_singleton_NoDup in Hosub;
            [|apply idsOf_NoDup, HminsV].
          destruct Hosub; [exfalso; auto|subst].
          eapply RqRsDownMatch_rs_rq in H6; [|rewrite <-H17; left; reflexivity].
          destruct H6 as [cidx [down ?]]; dest.
          disc_rule_conds.
          solve_midx_false.
        }

        (** Need to have just one child of the incoming RsUp messages. *)
        assert (exists rsFrom rsfm, In (rsFrom, rsfm) rins).
        { destruct rins as [|[rsFrom rsfm] ?]; [exfalso; auto|].
          do 2 eexists; left; reflexivity.
        }
        destruct H15 as [rsFrom [rsfm ?]].
        pose proof H8.
        rewrite Forall_forall in H16.
        specialize (H16 _ H15); simpl in H16.
        assert (In rsFrom (idsOf rins))
          by (apply in_map with (f:= idOf) in H15; assumption).
        pose proof H6.
        eapply RqRsDownMatch_rs_rq in H19; [|rewrite <-H17; eassumption]; clear H18.
        destruct H19 as [ccidx [down ?]]; dest.
        eapply Hosub in H15.
        assert (In rsFrom (idsOf eouts))
          by (apply in_map with (f:= idOf) in H15; assumption).
        pose proof (atomic_rsUp_out_in_history
                      Hiorqs Hrrs Hatm Hrch Hsteps _ H21 H23); clear H23.

        destruct (in_dec idx_dec (obj_idx obj) (oindsOf hst)).
        + (** If the history has visited the join *)
          assert (~ UpLockedNew (st_orqs st0) orqs (obj_idx obj)) as Hnul.
          { rewrite Forall_forall in H10; specialize (H10 _ H15).
            destruct H10 as [oidx ?].
            destruct H10; [destruct H10; disc_rule_conds; solve_midx_false|].
            red in H10; dest; disc_rule_conds.
            intro Hx.
            specialize (H25 _ i Hx).
            elim H25; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
          }

          eapply MsgOutsRqDownRsUp.
          * (** [RqDownRsUpDisj] *)
            eapply rqDownRsUpDisj_children_up_parent; eauto.
            { eapply rqDown_rsUp_inv_msg; eauto. }
            { right; red; eauto. }
            { apply HminsV. }
            { eapply rsUp_no_other_messages_in; eauto.
              { apply HminsV. }
              { apply H11; [assumption|apply Hnul|simpl_locks]. }
              { left; congruence. }
              { eapply rqDown_rsUp_inv_msg; eassumption. }
            }

          * (** Invariant for each message *)
            apply Forall_app.
            { apply Forall_forall.
              intros [midx msg] ?.
              apply removeL_In_NoDup in H23;
                [|apply idsOf_NoDup, rqDownRsUpDisj_NoDup; auto;
                  eapply rqDown_rsUp_inv_msg; eauto]; dest.
              rewrite Forall_forall in H10; pose proof (H10 _ H25).
              destruct H26 as [oidx ?]; destruct H26.
              { exists oidx; left.
                red in H26; dest.
                red; repeat ssplit; [assumption|..].
                { apply (DisjList_cons_inv idx_dec); [auto|].
                  eapply outside_parent_out; [apply Hrrs| |eassumption].
                  eapply rqDown_no_rsUp
                    with (eouts:= eouts)
                         (rqdm:= (midx, msg)) (orsum:= (rsFrom, rsfm)); eauto.
                  { eapply rqDown_rsUp_inv_msg, Forall_forall; eauto. }
                  { red; auto. }
                }
                { red; intros; icase uidx.
                  { simpl_locks. }
                  { simpl_locks; apply H28; assumption. }
                }
              }
              { exists oidx; right.
                red in H26; dest.
                red; repeat ssplit; [assumption|..].
                { red; intros; icase oidx0.
                  { split; simpl_locks. }
                  { specialize (H27 _ H29 H30); dest.
                    split; simpl_locks.
                  }
                }
                { red; intros; icase uidx.
                  { simpl_locks. }
                  { simpl_locks; apply H28; assumption. }
                }
              }
            }
            { repeat constructor.
              exists (obj_idx obj); right.
              red; repeat ssplit; [red; auto|..].
              { red; intros; icase oidx; [split; simpl_locks|].
                apply subtreeIndsOf_composed in H25; [|apply Hrrs].
                destruct H25; [exfalso; auto|].
                destruct H25 as [cidx [? ?]].
                pose proof (parentIdxOf_Some (proj1 (proj2 H)) _ H25).
                destruct H27 as [crqUp [crsUp [cdown ?]]]; dest.
                destruct (in_dec idx_dec crsUp (map fst rqi.(rqi_rss))).
                { rewrite <-H17 in i0.
                  apply in_map_iff in i0.
                  destruct i0 as [[crsUp' crsm] [? ?]]; simpl in *; subst.
                  apply Hosub in H31.
                  rewrite Forall_forall in H10; specialize (H10 _ H31).
                  destruct H10 as [rcidx ?].
                  destruct H10; [destruct H10; disc_rule_conds; solve_midx_false|].
                  red in H10; dest; disc_rule_conds.
                  specialize (H30 _ H23 H26); dest.
                  split; simpl_locks.
                }
                { assert (DownLocked orqs (obj_idx obj) rqi) by simpl_locks.
                  assert (rqi_midx_rsb rqi <> Some cdown)
                    by (intro Hx; rewrite Hx in *; inv H2; solve_midx_false).
                  specialize (H11 _ _ i Hnul H30).
                  specialize (H11 _ _ _ H25 H28 H29 n0 H31).
                  exfalso; destruct (H11 oidx); eauto.
                }
              }
              { rewrite Forall_forall in H10; specialize (H10 _ H15).
                destruct H10 as [oidx ?].
                destruct H10; [destruct H10; disc_rule_conds; solve_midx_false|].
                red in H10; dest; disc_rule_conds.
                red; intros; icase uidx; [simpl_locks|].
                simpl_locks.
                specialize (H25 _ H21 H27).
                eapply outside_parent_out; [apply Hrrs|..]; eassumption.
              }
            }

          * (** [DownLocksCoverInv] *)
            red; intros; icase oidx; [exfalso; simpl_locks|].
            simpl_locks.
            red; intros.
            specialize (H11 _ _ H23 H25 H26 _ _ _ H27 H28 H29 H30 H31).
            apply (DisjList_cons_inv idx_dec); [auto|].
            eapply outside_parent_out; [apply Hrrs| |eassumption].
            eapply DisjList_In_2; eassumption.

          * (** [DownLockRootInv] *)
            intros.
            destruct (idx_dec roidx (obj_idx obj)); subst.
            1: {
              red in H23; dest.
              simpl_locks; solve_midx_false.
            }
            assert (DownLockRoot (oindsOf hst) (st_orqs st0) orqs
                                 roidx rrqid orcidx).
            { red in H23; dest.
              destruct H23; [exfalso; auto|].
              red; repeat ssplit; try assumption.
              { intro Hx; elim H25.
                eapply upLockedNew_index_eq_1 with (orqs2:= orqs);
                  [mred|assumption].
              }
              { simpl_locks. }
            }
            specialize (H13 _ _ _ H25); clear H25.
            red in H13; dest.
            pose proof H13.
            red in H27; rewrite Forall_forall in H27.
            specialize (H27 _ H15).
            red in H27; dest; clear H27.
            assert (RsUpMsgFrom ccidx (rsFrom, rsfm)) by (red; auto).
            specialize (H28 _ _ H27 H19); dest.

            red; repeat ssplit.
            { (* [OutsInRoot] *)
              apply Forall_app.
              { apply forall_removeL; assumption. }
              { constructor; [|constructor].
                red; split; [red; intros; disc_rule_conds|].
                red; intros; disc_rule_conds; split.
                { eapply inside_parent_in; [apply Hrrs|..]; try eassumption.
                  intro Hx; subst.
                  red in H22; dest.
                  simpl_locks.
                }
                { destruct orcidx as [rcidx|]; [simpl in *|auto].
                  eapply outside_parent_out; [apply Hrrs|..]; eassumption.
                }
              }
            }

            { destruct orcidx as [rcidx|]; [simpl in *; dest|auto].
              repeat ssplit.
              { (* [DisjExceptUpLocked] *)
                red; intros; icase oidx;
                  [eapply outside_parent_out; [apply Hrrs|..]; eassumption|].
                eapply H25; eauto.
                intro Hx; elim H33.
                eapply upLockedNew_index_eq_1; [mred|eassumption].
              }
              { (* [UpLockCoverInv] *)
                red; intros; icase oidx;
                  [exfalso; eapply outside_parent_out; [apply Hrrs|..]; eauto|].
                mred; apply (DisjList_cons_inv idx_dec).
                { eapply H30; eauto. }
                { intro Hx.
                  eapply subtreeIndsOf_child_SubList in H36; [|apply Hrrs].
                  eapply subtreeIndsOf_SubList in H32; [|apply Hrrs].
                  apply H36, H32 in Hx.
                  eapply outside_parent_out; [apply Hrrs|..]; eauto.
                }
              }
              { (* [UpLockedBound] *)
                red; intros; icase oidx; [simpl_locks|].
                simpl_locks.
                apply H31; assumption.
              }
            }
            { (* [NoDownLockOutside] *)
              red; intros; icase oidx; [simpl_locks|].
              simpl_locks.
              eapply H26; eauto.
            }

        + (** If the history never visited the join *)
          eapply atomic_separation_ok in n; eauto; try apply Hiorqs.
          destruct n.
          2: {
            exfalso.
            eapply DisjList_In_2 in H23; [|eassumption].
            elim H23; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
          }
          destruct H23 as [cidx [? ?]].
          destruct (idx_dec cidx ccidx); subst.
          2: {
            apply H25 in H24.
            exfalso.
            eapply subtreeIndsOf_other_child_not_in
              with (cidx1:= ccidx) (cidx2:= cidx) (pidx:= obj_idx obj);
              try apply Hrrs; eauto.
          }

          assert (RsUpMsgOutInv (oindsOf hst) (st_orqs st0) orqs ccidx (rsFrom, rsfm)).
          { rewrite Forall_forall in H10.
            specialize (H10 _ H15); destruct H10 as [oidx ?].
            destruct H10; [destruct H10; disc_rule_conds|].
            destruct H10; disc_rule_conds.
            split; [red; auto|assumption].
          }
          assert (eouts = [(rsFrom, rsfm)]); subst.
          { eapply rsUp_outs_case_isolated; eauto.
            eapply rqDown_rsUp_inv_msg; eauto.
          }

          destruct HminsV.
          eapply SubList_singleton_NoDup in Hosub;
            [|apply idsOf_NoDup, HminsV].
          destruct Hosub; [exfalso; auto|subst].
          rewrite removeL_nil in *; simpl in *.
          red in H26; dest.

          eapply MsgOutsRqDownRsUp.
          * apply rqDownRsUpDisj_singleton.
          * repeat constructor.
            exists (obj_idx obj); right.
            red; repeat ssplit; [red; auto|..].
            { red; intros; icase oidx.
              { split.
                { intro Hx.
                  eapply steps_not_in_history_no_new_uplocks with (oidx:= obj_idx obj); eauto.
                  { intro Hx0; apply H25 in Hx0.
                    eapply parent_not_in_subtree; [apply Hrrs|..]; eassumption.
                  }
                  { simpl_locks; assumption. }
                }
                { simpl_locks. }
              }
              { specialize (H29 _ H31 (H25 _ H31)); dest.
                split; simpl_locks.
              }
            }
            { red; intros; icase uidx.
              { exfalso.
                eapply steps_not_in_history_no_new_uplocks with (oidx:= obj_idx obj); eauto.
                { intro Hx; apply H25 in Hx.
                  eapply parent_not_in_subtree; [apply Hrrs|..]; eassumption.
                }
                { simpl_locks; assumption. }
              }
              { simpl_locks.
                specialize (H30 _ H31 H32).
                eapply outside_parent_out; [apply Hrrs|..]; eassumption.
              }
            }
          * red; intros; icase oidx; [exfalso; simpl_locks|].
            simpl_locks.
            red; intros.
            apply (DisjList_cons_inv idx_dec); [eapply H11; eauto|].
            apply H25 in H31.
            apply subtreeIndsOf_SubList in H31; [|apply Hrrs].
            apply subtreeIndsOf_child_SubList in H34; [|apply Hrrs].
            intro Hx.
            apply H34, H31 in Hx.
            eapply parent_not_in_subtree; [apply Hrrs|..]; eauto.

          * intros.
            destruct (idx_dec (obj_idx obj) roidx); subst;
              [exfalso; red in H31; dest; simpl_locks|].
            assert (DownLockRoot (oindsOf hst) (st_orqs st0) orqs
                                 roidx rrqid orcidx).
            { red in H31; dest.
              red; repeat ssplit; try eassumption; simpl_locks.
              destruct H31; [exfalso; auto|assumption].
            }
            specialize (H13 _ _ _ H32); clear H31 H32.

            red in H13; dest.
            pose proof H13.
            red in H33; rewrite Forall_forall in H33.
            specialize (H33 _ (or_introl eq_refl)).
            red in H33; dest; clear H33.
            assert (RsUpMsgFrom ccidx (rsFrom, rsfm)) by (red; auto).
            specialize (H34 _ _ H33 H19); dest.

            red; repeat ssplit.
            { constructor; [|constructor].
              red; split; [red; intros; disc_rule_conds|].
              red; intros; disc_rule_conds; split.
              { eapply inside_parent_in; [apply Hrrs|..]; try eassumption. }
              { destruct orcidx as [rcidx|]; [simpl in *|auto].
                eapply outside_parent_out; [apply Hrrs|..]; eassumption.
              }
            }

            { destruct orcidx as [rcidx|]; [simpl in *; dest|auto].
              repeat ssplit.
              { red; intros; icase oidx;
                  [eapply outside_parent_out; [apply Hrrs|..]; eassumption|].
                eapply H31; eauto.
                intro Hx; elim H39.
                eapply upLockedNew_index_eq_1; [mred|eassumption].
              }
              { red; intros; icase oidx;
                  [exfalso; eapply outside_parent_out; [apply Hrrs|..]; eauto|].
                mred; apply (DisjList_cons_inv idx_dec).
                { eapply H36; eauto. }
                { intro Hx.
                  eapply subtreeIndsOf_child_SubList in H42; [|apply Hrrs].
                  eapply subtreeIndsOf_SubList in H38; [|apply Hrrs].
                  apply H42, H38 in Hx.
                  eapply outside_parent_out; [apply Hrrs|..]; eauto.
                }
              }
              { red; intros; exfalso.
                icase oidx.
                { eapply steps_not_in_history_no_new_uplocks with (oidx:= obj_idx obj); eauto.
                  { intro Hx; apply H25 in Hx.
                    eapply parent_not_in_subtree; [apply Hrrs|..]; eassumption.
                  }
                  { simpl; simpl_locks; assumption. }
                }
                { specialize (H29 _ H38 (H25 _ H38)); dest.
                  simpl_locks.
                }
              }
            }
            { red; intros; icase oidx; [simpl_locks|].
              simpl_locks.
              eapply H32; eauto.
            }

      - (** [RsUpUp-silent] *)
        inv_MsgOutsInv.
        1: { exfalso; apply SubList_nil_inv in Hosub; auto. }
        1: {
          exfalso.
          eapply SubList_singleton_NoDup in Hosub;
            [|apply idsOf_NoDup, HminsV].
          destruct Hosub; [exfalso; auto|subst].
          eapply RqRsDownMatch_rs_rq in H4; [|rewrite <-H17; left; reflexivity].
          destruct H4 as [cidx [down ?]]; dest.
          disc_rule_conds.
        }
        1: {
          exfalso.
          eapply SubList_singleton_NoDup in Hosub;
            [|apply idsOf_NoDup, HminsV].
          destruct Hosub; [exfalso; auto|subst].
          eapply RqRsDownMatch_rs_rq in H4; [|rewrite <-H17; left; reflexivity].
          destruct H4 as [cidx [down ?]]; dest.
          disc_rule_conds.
          solve_midx_false.
        }

        (** Need to have just one child of the incoming RsUp messages. *)
        assert (exists rsFrom rsfm, In (rsFrom, rsfm) rins).
        { destruct rins as [|[rsFrom rsfm] ?]; [exfalso; auto|].
          do 2 eexists; left; reflexivity.
        }
        destruct H10 as [rsFrom [rsfm ?]].
        pose proof H8.
        rewrite Forall_forall in H11.
        specialize (H11 _ H10); simpl in H11.
        assert (In rsFrom (idsOf rins))
          by (apply in_map with (f:= idOf) in H10; assumption).
        pose proof H4.
        eapply RqRsDownMatch_rs_rq in H15; [|rewrite <-H17; eassumption]; clear H13.
        destruct H15 as [ccidx [down ?]]; dest.
        eapply Hosub in H10.
        assert (In rsFrom (idsOf eouts))
          by (apply in_map with (f:= idOf) in H10; assumption).
        pose proof (atomic_rsUp_out_in_history
                      Hiorqs Hrrs Hatm Hrch Hsteps _ H18 H20); clear H20.

        destruct (in_dec idx_dec (obj_idx obj) (oindsOf hst)).
        + (** If the history has visited the join *)
          assert (~ UpLockedNew (st_orqs st0) orqs (obj_idx obj)) as Hnul.
          { rewrite Forall_forall in H6; specialize (H6 _ H10).
            destruct H6 as [oidx ?].
            destruct H6; [destruct H6; disc_rule_conds; solve_midx_false|].
            red in H6; dest; disc_rule_conds.
            intro Hx.
            specialize (H22 _ i Hx).
            elim H22; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
          }

          rewrite app_nil_r.
          eapply MsgOutsRqDownRsUp;
            [apply rqDownRsUpDisj_removeL; auto|..].

          * (** Invariant for each message *)
            apply Forall_forall.
            intros [midx msg] ?.
            apply removeL_In_NoDup in H20;
              [|apply idsOf_NoDup, rqDownRsUpDisj_NoDup; auto;
                eapply rqDown_rsUp_inv_msg; eauto]; dest.
            rewrite Forall_forall in H6; pose proof (H6 _ H22).
            destruct H23 as [oidx ?]; destruct H23.
            { exists oidx; left.
              red in H23; dest.
              red; repeat ssplit; [assumption|..].
              { apply (DisjList_cons_inv idx_dec); [auto|].
                eapply outside_parent_out; [apply Hrrs| |eassumption].
                eapply rqDown_no_rsUp
                  with (eouts:= eouts)
                       (rqdm:= (midx, msg)) (orsum:= (rsFrom, rsfm)); eauto.
                { eapply rqDown_rsUp_inv_msg, Forall_forall; eauto. }
                { red; auto. }
              }
              { red; intros; icase uidx.
                { simpl_locks. }
                { simpl_locks; apply H25; assumption. }
              }
            }
            { exists oidx; right.
              red in H23; dest.
              red; repeat ssplit; [assumption|..].
              { red; intros; icase oidx0.
                { split; simpl_locks. }
                { specialize (H24 _ H26 H27); dest.
                  split; simpl_locks.
                }
              }
              { red; intros; icase uidx.
                { simpl_locks. }
                { simpl_locks; apply H25; assumption. }
              }
            }

          * (** [DownLocksCoverInv] *)
            red; intros; icase oidx; [exfalso; simpl_locks|].
            simpl_locks.
            red; intros.
            specialize (H7 _ _ H20 H22 H23 _ _ _ H24 H25 H26 H27 H28).
            apply (DisjList_cons_inv idx_dec); [auto|].
            eapply outside_parent_out; [apply Hrrs| |eassumption].
            eapply DisjList_In_2; eassumption.

          * (** [DownLockRootInv] *)
            intros.
            destruct (idx_dec roidx (obj_idx obj)); subst.
            1: {
              red in H20; dest.
              simpl_locks; solve_midx_false.
            }
            assert (DownLockRoot (oindsOf hst) (st_orqs st0) orqs
                                 roidx rrqid orcidx).
            { red in H20; dest.
              destruct H20; [exfalso; auto|].
              red; repeat ssplit; try assumption.
              { intro Hx; elim H22.
                eapply upLockedNew_index_eq_1 with (orqs2:= orqs);
                  [mred|assumption].
              }
              { simpl_locks. }
            }
            specialize (H9 _ _ _ H22); clear H22.
            red in H9; dest.
            pose proof H9.
            red in H24; rewrite Forall_forall in H24.
            specialize (H24 _ H10).
            red in H24; dest; clear H24.
            assert (RsUpMsgFrom ccidx (rsFrom, rsfm)) by (red; auto).
            specialize (H25 _ _ H24 H15); dest.

            red; repeat ssplit.
            { (* [OutsInRoot] *)
              apply forall_removeL; assumption.
            }

            { destruct orcidx as [rcidx|]; [simpl in *; dest|auto].
              repeat ssplit.
              { (* [DisjExceptUpLocked] *)
                red; intros; icase oidx;
                  [eapply outside_parent_out; [apply Hrrs|..]; eassumption|].
                eapply H22; eauto.
                intro Hx; elim H30.
                eapply upLockedNew_index_eq_1; [mred|eassumption].
              }
              { (* [UpLockCoverInv] *)
                red; intros; icase oidx;
                  [exfalso; eapply outside_parent_out; [apply Hrrs|..]; eauto|].
                mred; apply (DisjList_cons_inv idx_dec).
                { eapply H27; eauto. }
                { intro Hx.
                  eapply subtreeIndsOf_child_SubList in H33; [|apply Hrrs].
                  eapply subtreeIndsOf_SubList in H29; [|apply Hrrs].
                  apply H33, H29 in Hx.
                  eapply outside_parent_out; [apply Hrrs|..]; eauto.
                }
              }
              { (* [UpLockedBound] *)
                red; intros; icase oidx; [simpl_locks|].
                simpl_locks.
                apply H28; assumption.
              }
            }
            { (* [NoDownLockOutside] *)
              red; intros; icase oidx; [simpl_locks|].
              simpl_locks.
              eapply H23; eauto.
            }

        + (** If the history never visited the join *)
          eapply atomic_separation_ok in n; eauto; try apply Hiorqs.
          destruct n.
          2: {
            exfalso.
            eapply DisjList_In_2 in H20; [|eassumption].
            elim H20; apply subtreeIndsOf_child_in; [apply Hrrs|assumption].
          }
          destruct H20 as [cidx [? ?]].
          destruct (idx_dec cidx ccidx); subst.
          2: {
            apply H22 in H21.
            exfalso.
            eapply subtreeIndsOf_other_child_not_in
              with (cidx1:= ccidx) (cidx2:= cidx) (pidx:= obj_idx obj);
              try apply Hrrs; eauto.
          }

          assert (RsUpMsgOutInv (oindsOf hst) (st_orqs st0) orqs ccidx (rsFrom, rsfm)).
          { rewrite Forall_forall in H6.
            specialize (H6 _ H10); destruct H6 as [oidx ?].
            destruct H6; [destruct H6; disc_rule_conds|].
            destruct H6; disc_rule_conds.
            split; [red; auto|assumption].
          }
          assert (eouts = [(rsFrom, rsfm)]); subst.
          { eapply rsUp_outs_case_isolated; eauto.
            eapply rqDown_rsUp_inv_msg; eauto.
          }

          destruct HminsV.
          eapply SubList_singleton_NoDup in Hosub;
            [|apply idsOf_NoDup, HminsV].
          destruct Hosub; [exfalso; auto|subst].
          rewrite removeL_nil in *; simpl in *.
          constructor.
    Qed.

  End InternalStep.

  Lemma atomic_msg_outs_ok:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        MsgOutsInv (oindsOf hst) s1.(st_orqs) s2.(st_orqs) eouts.
  Proof.
    destruct Hrrs as [? [? [_ ?]]].
    induction 1; simpl; intros; subst;
      [inv_steps; eapply step_msg_outs_ok; eauto|].
    inv_steps.
    specialize (IHAtomic _ _ H8 H10).
    assert (Reachable (steps step_m) sys st2) by eauto.
    pose proof (footprints_ok Hiorqs H0 H5) as Hftinv.
    pose proof (downLockInv_ok Hiorqs H0 H H1 H5) as Hdlinv.
    clear H5.
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule; simpl in *.
    - eapply step_msg_outs_ok_ImmDownRule; eauto.
    - eapply step_msg_outs_ok_ImmUpRule; eauto.
    - eapply step_msg_outs_ok_RqFwdRule; eauto.
    - eapply step_msg_outs_ok_RsBackRule; eauto.
    - eapply step_msg_outs_ok_RsDownRqDownRule; eauto.
  Qed.

  Corollary atomic_rqDown_covers:
    forall oidx rqDown,
      RqDownMsgTo oidx rqDown ->
      forall inits ins hst outs eouts,
        In rqDown eouts ->
        Atomic inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          steps step_m sys st1 hst st2 ->
          DisjList (oindsOf hst) (subtreeIndsOf dtr oidx).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    eapply atomic_msg_outs_ok in H4; eauto.
    inv H4.
    - dest_in.
    - exfalso.
      dest_in.
      destruct H7.
      repeat disc_msg_case.
      solve_midx_false.
    - exfalso.
      dest_in.
      destruct H7.
      repeat disc_msg_case.
      rewrite H2 in H3; discriminate.
    - rewrite Forall_forall in H8.
      specialize (H8 _ H3).
      destruct H8 as [doidx ?].
      destruct H4.
      + red in H4; dest.
        repeat disc_msg_case.
        disc_rule_conds.
      + exfalso.
        red in H4; dest.
        repeat disc_msg_case.
        solve_midx_false.
  Qed.

  Corollary atomic_rsDown_covers:
    forall oidx rsDown,
      RsDownMsgTo oidx rsDown ->
      forall inits ins hst outs eouts,
        In rsDown eouts ->
        Atomic inits ins hst outs eouts ->
        Forall (NonRqUpL dtr) hst ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          steps step_m sys st1 hst st2 ->
          DisjList (oindsOf hst) (subtreeIndsOf dtr oidx).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof H4.
    eapply atomic_msg_outs_ok in H8; eauto.
    inv H8.
    - dest_in.
    - exfalso.
      dest_in.
      destruct H9.
      repeat disc_msg_case.
      solve_midx_false.
    - dest_in.
      red in H9; dest.
      repeat disc_msg_case.
      repeat disc_rule_minds.
      eapply disjExceptUpLocked_no_UpLockedNew_disj; [eassumption|].
      eapply atomic_NonRqUp_no_new_uplocks; eauto.
    - exfalso.
      rewrite Forall_forall in H10.
      specialize (H10 _ H3).
      destruct H10 as [doidx ?].
      destruct H8.
      + destruct H8.
        repeat disc_msg_case.
        rewrite H2 in H8; discriminate.
      + destruct H8.
        repeat disc_msg_case.
        solve_midx_false.
  Qed.

End Coverage.

Ltac disc_msg_case :=
  match goal with
  | [H: RqUpMsgFrom _ _ _ |- _] => destruct H
  | [H: RsDownMsgTo _ _ _ |- _] => destruct H
  | [H: RqDownMsgTo _ _ _ |- _] => destruct H
  | [H: RsUpMsgFrom _ _ _ |- _] => destruct H
  end.

Close Scope list.
Close Scope fmap.
