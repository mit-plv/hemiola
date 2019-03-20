Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial SerialFacts.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvMsg RqRsInvLock RqRsInvSep.
Require Import RqUpRed.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

(* Fixpoint UniqueIn {A} (a: A) (l: list A) := *)
(*   match l with *)
(*   | nil => False *)
(*   | b :: m => (b = a /\ ~ In a m) \/ (b <> a /\ UniqueIn a m) *)
(*   end. *)

Section Coverage.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).
  Hypothesis (Hrrs: RqRsSys dtr sys).

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

    Definition NoUpLock (oidx: IdxT) :=
      orqs2@[oidx] >>=[True] (fun orq => orq@[upRq] = None).

    Definition NoDownLock (oidx: IdxT) :=
      orqs2@[oidx] >>=[True] (fun orq => orq@[downRq] = None).

    Definition NoDownLocks := 
      forall oidx, In oidx oinds -> NoDownLock oidx.

    Definition NoDownLocks2 (oinds2: list IdxT) :=
      forall oidx,
        In oidx oinds ->
        In oidx oinds2 ->
        NoDownLock oidx.

    Definition IndsInTree (ridx: IdxT) :=
      SubList oinds (subtreeIndsOf dtr ridx).
    
    Definition IndsDisjTree (ridx: IdxT) :=
      DisjList oinds (subtreeIndsOf dtr ridx).

    Definition UpLocked (oidx: IdxT) :=
      orqs2@[oidx] >>=[False] (fun orq2 => orq2@[upRq] <> None).

    Definition UpLockedNew (oidx: IdxT) :=
      orqs2@[oidx] >>=[False]
           (fun orq2 =>
              orq2@[upRq] <> None /\
              orqs1@[oidx] >>=[True] (fun orq1 => orq1@[upRq] = None)).

    Definition DownLocked (oidx: IdxT) (rqid: RqInfo Msg) :=
      orqs2@[oidx] >>=[False]
           (fun orq2 => orq2@[downRq] = Some rqid).

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
            down <> rqiu.(rqi_midx_rsb) ->
            IndsDisjTree cidx.

    Definition DisjExceptUpLocked (tidx: IdxT) :=
      forall oidx,
        In oidx oinds ->
        ~ UpLockedNew oidx ->
        ~ In oidx (subtreeIndsOf dtr tidx).

    Definition RqUpMsgOutInv (oidx: IdxT) (rqUp: Id Msg) :=
      RqUpMsgFrom oidx rqUp /\
      UpLockCoverInv oidx.

    Definition RsDownMsgOutInv (oidx: IdxT) (rsDown: Id Msg) :=
      RsDownMsgTo oidx rsDown /\
      DisjExceptUpLocked oidx /\
      UpLockCoverInv oidx.

    Definition RqDownMsgOutInv (oidx: IdxT) (rqDown: Id Msg) :=
      RqDownMsgTo oidx rqDown /\ IndsDisjTree oidx.

    Definition RsUpMsgOutInv (oidx: IdxT) (rsUp: Id Msg) :=
      RsUpMsgFrom oidx rsUp /\ NoDownLocks2 (subtreeIndsOf dtr oidx).

    Definition NoDownLockRoot :=
      forall oidx,
        In oidx oinds ->
        UpLocked oidx \/ NoDownLock oidx.
    
    (* The root of downlocks is the one that also has a downlock but
     * the return index ([rqi_midx_rsb]) is one of children.
     *)
    Definition DownLockRoot
               (roidx: IdxT) (rorq: ORq Msg)
               (rrqid: RqInfo Msg) (rcidx: IdxT) :=
      In roidx oinds /\
      NoUpLock roidx /\ DownLocked roidx rrqid /\
      parentIdxOf dtr rcidx = Some roidx /\
      edgeDownTo dtr rcidx = Some (rrqid.(rqi_midx_rsb)).

    Definition DownLockCoverInv (oidx: IdxT) (rqid: RqInfo Msg) :=
      forall cidx rsUp down,
        parentIdxOf dtr cidx = Some oidx ->
        rsEdgeUpFrom dtr cidx = Some rsUp ->
        edgeDownTo dtr cidx = Some down ->
        ~ In rsUp rqid.(rqi_minds_rss) ->
        down <> rqid.(rqi_midx_rsb) ->
        IndsDisjTree cidx.

    Definition DownLocksCoverInv (roidx: IdxT) (rcidx: IdxT) :=
      forall oidx rqid,
        In oidx oinds ->
        In oidx (subtreeIndsOf dtr roidx) ->
        ~ In oidx (subtreeIndsOf dtr rcidx) ->
        DownLocked oidx rqid ->
        DownLockCoverInv oidx rqid.
    
    Definition RqDownInRoot (roidx: IdxT) (rcidx: IdxT) (eout: Id Msg) :=
      forall oidx,
        RqDownMsgTo oidx eout ->
        In oidx (subtreeIndsOf dtr roidx) /\
        ~ In oidx (subtreeIndsOf dtr rcidx).

    Definition RsUpInRoot (roidx: IdxT) (rcidx: IdxT) (eout: Id Msg) :=
      forall oidx,
        RsUpMsgFrom oidx eout ->
        In oidx (subtreeIndsOf dtr roidx) /\
        ~ In oidx (subtreeIndsOf dtr rcidx).

    Definition OutInRoot (roidx: IdxT) (rcidx: IdxT) (eout: Id Msg) :=
      RqDownInRoot roidx rcidx eout /\ RsUpInRoot roidx rcidx eout.

    Definition OutsInRoot (roidx: IdxT) (rcidx: IdxT) (eouts: list (Id Msg)) :=
      Forall (OutInRoot roidx rcidx) eouts.

    Definition DownLockRootInv (roidx: IdxT) (rcidx: IdxT) (eouts: list (Id Msg)) :=
      OutsInRoot roidx rcidx eouts /\
      DisjExceptUpLocked rcidx /\
      UpLockCoverInv rcidx /\
      DownLocksCoverInv roidx rcidx.

    Inductive MsgOutsCases: list (Id Msg) -> Prop :=
    | MsgOutsRqUp: (* Only one live RqUp message *)
        forall oidx rqUp,
          RqUpMsgOutInv oidx rqUp ->
          UpLockedTotal ->
          MsgOutsCases [rqUp]
    | MsgOutsRsDown: (* Only one live RsDown message *)
        forall oidx rsDown,
          RsDownMsgOutInv oidx rsDown ->
          NoDownLockRoot ->
          MsgOutsCases [rsDown]
    | MsgOutsRqDownRsUp: (* RqDown or RsUp messages *)
        forall eouts,
          NoDup (idsOf eouts) ->
          Forall (fun eout =>
                    exists oidx,
                      RqDownMsgOutInv oidx eout \/
                      RsUpMsgOutInv oidx eout) eouts ->
          (forall roidx rorq rrqid rcidx,
              DownLockRoot roidx rorq rrqid rcidx ->
              DownLockRootInv roidx rcidx eouts) ->
          MsgOutsCases eouts.

  End OnAtomic.

  (*! Facts *)

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_messages_in;
    try disc_msg_case.

  Lemma disjExceptUpLocked_no_UpLockedNew_disj:
    forall oinds orqs1 orqs2 tidx,
      DisjExceptUpLocked oinds orqs1 orqs2 tidx ->
      Forall (fun oidx => ~ UpLockedNew orqs1 orqs2 oidx) oinds ->
      DisjList oinds (subtreeIndsOf dtr tidx).
  Proof.
    unfold DisjExceptUpLocked; intros.
    apply (DisjList_false_spec eq_nat_dec).
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
      ~ UpLockedNew st1.(bst_orqs) st2.(bst_orqs) oidx.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H2).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule; simpl in *.

    - disc_rule_conds.
      intro Hx; red in Hx; repeat (simpl in Hx; mred).

    - disc_rule_conds.
      intro Hx; red in Hx; repeat (simpl in Hx; mred).
      dest; congruence.

    - disc_rule_conds.
      + pose proof (rqEdgeUpFrom_Some H _ H7).
        destruct H15 as [rsUp [down [pidx ?]]]; dest.
        elim (H4 pidx).
        red; do 2 eexists; eauto.
      + intro Hx; red in Hx; repeat (simpl in Hx; mred).
      + intro Hx; red in Hx; repeat (simpl in Hx; mred).

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + intro Hx; red in Hx; repeat (simpl in Hx; mred).
      + intro Hx; red in Hx; repeat (simpl in Hx; mred).
      + intro Hx; red in Hx; repeat (simpl in Hx; mred).

    - disc_rule_conds.
      intro Hx; red in Hx; repeat (simpl in Hx; mred).
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

  Lemma atomic_NonRqUp_no_new_uplocks:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      Forall (NonRqUpL dtr) hst ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        Forall (fun oidx => ~ UpLockedNew s1.(bst_orqs) s2.(bst_orqs) oidx)
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
      + destruct (in_dec eq_nat_dec oidx (oindsOf hst)).
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
        destruct (eq_nat_dec uidx oidx); subst.
        * eapply upLockedNew_not_trans; eauto.
          eapply step_NonRqUp_no_new_uplocks; eauto.
        * intros; intro Hx.
          elim IHAtomic.
          rewrite upLockedNew_index_eq_1; [eassumption|].
          eapply steps_locks_unaffected.
          { eapply steps_singleton; eassumption. }
          { simpl; intros; intuition auto. }
  Qed.
  
  Lemma noDownLock_orqs_downRq_remove:
    forall oidx orqs ridx rorq,
      NoDownLock orqs oidx ->
      NoDownLock (orqs +[ridx <- rorq -[downRq]]) oidx.
  Proof.
    unfold NoDownLock; intros.
    destruct (eq_nat_dec ridx oidx); subst; repeat (simpl; mred).
  Qed.

  Lemma noDownLocks2_orqs_downRq_remove:
    forall oinds tinds orqs ridx rorq,
      NoDownLocks2 oinds orqs tinds ->
      NoDownLocks2 oinds (orqs +[ridx <- rorq -[downRq]]) tinds.
  Proof.
    unfold NoDownLocks2; intros.
    eapply noDownLock_orqs_downRq_remove; auto.
  Qed.

  Lemma rsUpMsgOutInv_orqs_downRq_remove:
    forall oidx rsUp orqs oinds ridx rorq,
      RsUpMsgOutInv oinds orqs oidx rsUp ->
      RsUpMsgOutInv oinds (orqs +[ridx <- rorq -[downRq]]) oidx rsUp.
  Proof.
    intros; destruct H.
    split; [assumption|].
    apply noDownLocks2_orqs_downRq_remove; auto.
  Qed.
  
  Lemma noDownLocks2_oinds_tl:
    forall oinds oidx tinds orqs,
      NoDownLocks2 (oidx :: oinds) orqs tinds ->
      NoDownLocks2 oinds orqs tinds.
  Proof.
    unfold NoDownLocks2; intros; firstorder.
  Qed.

  Lemma rsUpMsgOutInv_oinds_tl:
    forall ridx rsUp orqs oinds oidx,
      RsUpMsgOutInv (oidx :: oinds) orqs ridx rsUp ->
      RsUpMsgOutInv oinds orqs ridx rsUp.
  Proof.
    unfold RsUpMsgOutInv; intros; dest.
    split; auto.
    eapply noDownLocks2_oinds_tl; eauto.
  Qed.

  Lemma downLockCoverInv_oinds_tl:
    forall ridx rqi oinds oidx,
      DownLockCoverInv (oidx :: oinds) ridx rqi ->
      DownLockCoverInv oinds ridx rqi.
  Proof.
    unfold DownLockCoverInv; intros.
    specialize (H _ _ _ H0 H1 H2 H3).
    apply DisjList_cons in H; dest; auto.
  Qed.

  Lemma msgOutsCases_NoDup:
    forall oinds orqs1 orqs2 eouts,
      MsgOutsCases oinds orqs1 orqs2 eouts ->
      NoDup (idsOf eouts).
  Proof.
    intros; inv H.
    - repeat constructor; auto.
    - repeat constructor; auto.
    - assumption.
  Qed.
  
  Lemma step_msg_outs_ok:
    forall st1 st2 oidx ridx rins routs,
      Reachable (steps step_m) sys st1 ->
      step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
      MsgOutsCases [oidx] st1.(bst_orqs) st2.(bst_orqs) routs.
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    pose proof (footprints_ok H0 H2).
    inv_step.
    good_rqrs_rule_get rule.
    good_rqrs_rule_cases rule; simpl in *.

    - disc_rule_conds.
      eapply MsgOutsRsDown.
      red; repeat ssplit.
      + red; eauto.
      + red; intros; Common.dest_in.
        apply parent_not_in_subtree; [apply Hrrs|]; assumption.
      + red; intros; Common.dest_in; mred.
      + red; intros; Common.dest_in.
        right; red; mred.

    - disc_rule_conds.
      eapply MsgOutsRqDownRsUp.
      + repeat constructor; auto.
      + repeat constructor.
        eexists; right.
        split; [red; eauto|].
        red; intros; Common.dest_in.
        red; mred.
      + red; intros; Common.dest_in.
        red in H3; dest; Common.dest_in.
        red in H7; mred; simpl in H7; congruence.

    - disc_rule_conds.
      + eapply MsgOutsRqUp.
        * split; [red; eauto|].
          red; intros; Common.dest_in.
          red; apply (DisjList_singleton_1 eq_nat_dec).
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * red; intros; Common.dest_in.
          red; repeat (simpl; mred).
          split; [discriminate|reflexivity].

      + eapply MsgOutsRqDownRsUp.
        * destruct H19; assumption.
        * apply Forall_forall; intros [midx msg] ?.
          rewrite Forall_forall in H32; specialize (H32 _ H5).
          apply in_map with (f:= idOf) in H5.
          eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
          destruct H20 as [cidx [rsUp ?]]; dest.
          eexists; left.
          split; [red; eauto|].
          red; apply (DisjList_singleton_1 eq_nat_dec).
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * intros.
          red in H5; dest; Common.dest_in.
          red in H23; repeat (simpl in H23; mred).
          red; repeat ssplit.
          { apply Forall_forall; intros [midx msg] ?.
            apply in_map with (f:= idOf) in H5.
            eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
            destruct H20 as [cidx [rsUp ?]]; dest.
            split.
            { red; intros; disc_rule_conds.
              split.
              { apply subtreeIndsOf_child_in; [apply Hrrs|assumption]. }
              { eapply subtreeIndsOf_other_child_not_in; [apply Hrrs|..]; eassumption. }
            }
            { red; intros; disc_rule_conds; solve_midx_false. }
          }
          { red; intros; Common.dest_in.
            apply parent_not_in_subtree; [apply Hrrs|]; assumption.
          }
          { red; intros; Common.dest_in.
            red; apply (DisjList_singleton_1 eq_nat_dec).
            intro Hx.
            apply subtreeIndsOf_child_SubList in H31; [|apply Hrrs].
            apply H31 in Hx.
            eapply parent_not_in_subtree; [apply Hrrs|..]; eauto.
          }
          { red; intros; Common.dest_in.
            red; intros.
            red; apply (DisjList_singleton_1 eq_nat_dec).
            apply parent_not_in_subtree; [apply Hrrs|]; assumption.
          }
          
      + eapply MsgOutsRqDownRsUp.
        * destruct H19; assumption.
        * apply Forall_forall; intros [midx msg] ?.
          rewrite Forall_forall in H32; specialize (H32 _ H7).
          apply in_map with (f:= idOf) in H7.
          eapply RqRsDownMatch_rq_rs in H6; [|eassumption].
          destruct H6 as [cidx [rsUp ?]]; dest.
          eexists; left.
          split; [red; eauto|].
          red; apply (DisjList_singleton_1 eq_nat_dec).
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * intros; exfalso.
          red in H7; dest; Common.dest_in.
          red in H14; repeat (simpl in H14; mred).
          solve_midx_false.

    - good_footprint_get (obj_idx obj).
      disc_rule_conds.
      + eapply MsgOutsRsDown.
        red; repeat ssplit; [red; eauto|..].
        * red; intros; Common.dest_in.
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * red; intros; Common.dest_in.
          red; apply (DisjList_singleton_1 eq_nat_dec).
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * red; intros; Common.dest_in.
          right; red; repeat (simpl; mred).
      + eapply MsgOutsRsDown.
        red; repeat ssplit; [red; eauto|..].
        * red; intros; Common.dest_in.
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * red; intros; Common.dest_in.
          red; apply (DisjList_singleton_1 eq_nat_dec).
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * red; intros; Common.dest_in.
          right; red; repeat (simpl; mred).

      + eapply MsgOutsRqDownRsUp.
        * repeat constructor; auto.
        * repeat constructor.
          eexists; right.
          split; [red; eauto|].
          red; intros; Common.dest_in.
          red; repeat (simpl; mred).
        * intros; exfalso.
          red in H11; dest; Common.dest_in.
          red in H22; repeat (simpl in H22; mred).

    - disc_rule_conds.
      eapply MsgOutsRqDownRsUp.
      + destruct H19; assumption.
      + apply Forall_forall; intros [midx msg] ?.
        rewrite Forall_forall in H27; specialize (H27 _ H5).
        apply in_map with (f:= idOf) in H5.
        eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
        destruct H20 as [cidx [rsUp ?]]; dest.
        eexists; left.
        split; [red; eauto|].
        apply (DisjList_singleton_1 eq_nat_dec).
        apply parent_not_in_subtree; [apply Hrrs|]; assumption.
      + intros.
        red in H5; dest; Common.dest_in.
        red in H23; repeat (simpl in H23; mred).
        red; repeat ssplit.
        * apply Forall_forall; intros [midx msg] ?.
          apply in_map with (f:= idOf) in H5.
          eapply RqRsDownMatch_rq_rs in H20; [|eassumption].
          destruct H20 as [cidx [rsUp ?]]; dest.
          split.
          { red; intros; disc_rule_conds.
            split.
            { apply subtreeIndsOf_child_in; [apply Hrrs|assumption]. }
            { eapply subtreeIndsOf_other_child_not_in; [apply Hrrs|..]; eassumption. }
          }
          { red; intros; disc_rule_conds; solve_midx_false. }
        * red; intros; Common.dest_in.
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
        * red; intros; Common.dest_in.
          red; apply (DisjList_singleton_1 eq_nat_dec).
          intro Hx.
          apply subtreeIndsOf_child_SubList in H30; [|apply Hrrs].
          apply H30 in Hx.
          eapply parent_not_in_subtree; [apply Hrrs|..]; eauto.
        * red; intros; Common.dest_in.
          red; intros.
          apply (DisjList_singleton_1 eq_nat_dec).
          apply parent_not_in_subtree; [apply Hrrs|]; assumption.
  Qed.

  Lemma rqDown_rsUp_inv_msg:
    forall orqs oinds eouts,
      Forall (fun eout =>
                exists oidx,
                  RqDownMsgOutInv oinds oidx eout \/
                  RsUpMsgOutInv oinds orqs oidx eout) eouts ->
      Forall (fun eout =>
                exists oidx,
                  RqDownMsgTo oidx eout \/
                  RsUpMsgFrom oidx eout) eouts.
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

  Lemma rqDownMsgOutInv_no_rqDown:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall oidx rqdm,
          In rqdm eouts ->
          RqDownMsgOutInv (oindsOf hst) oidx rqdm ->
          forall ooidx orqdm,
            RqDownMsgTo ooidx orqdm ->
            In orqdm eouts -> orqdm <> rqdm ->
            ~ In ooidx (subtreeIndsOf dtr oidx).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    destruct rqdm as [rqDown rqm].
    destruct orqdm as [orqDown orqm].
    disc_msg_case.
    pose proof (edgeDownTo_Some H _ H10).
    destruct H11 as [rqUp [rsUp [pidx ?]]]; dest.
    assert (In orqDown (idsOf eouts))
      by (apply in_map_iff; exists (orqDown, orqm); auto).
    pose proof (atomic_down_out_in_history
                  Hrrs H2 H3 H4 _ H10 H13 H14); clear H14.
    simpl in *.
    destruct H6 as [[? ?] ?]; simpl in *.
    pose proof (steps_object_in_system H4 _ H15).
    destruct H17 as [pobj [? ?]].

    intro Hx.
    eapply DisjList_In_2 in H15; [|eassumption].
    eapply inside_child_outside_parent_case in Hx;
      try eassumption; try apply Hrrs; subst.
    disc_rule_conds.

    pose proof (atomic_messages_eouts_in msg_dec H2 H4).
    rewrite Forall_forall in H10.
    pose proof (H10 _ H5).
    pose proof (H10 _ H8).
    pose proof (downLockInv_ok H0 H (reachable_steps H3 H4)).
    good_locking_get pobj.
    eapply downLockInvORq_down_rqsQ_length_two_False;
      try eassumption.
    eapply rqsQ_length_two;
      [eapply H6|eapply H7| | |]; eauto.
    intro Hx; subst; auto.
  Qed.

  Lemma rqDownMsgOutInv_no_rsUp:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall oidx rqdm,
          In rqdm eouts ->
          RqDownMsgOutInv (oindsOf hst) oidx rqdm ->
          forall ooidx opidx opobj orsum,
            parentIdxOf dtr ooidx = Some opidx ->
            In opobj sys.(sys_objs) ->
            opobj.(obj_idx) = opidx ->
            RsUpMsgFrom ooidx orsum ->
            In orsum eouts ->
            ~ In opidx (subtreeIndsOf dtr oidx).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    destruct rqdm as [rqDown rqm].
    destruct orsum as [rsUp rsm].
    disc_msg_case.
    assert (In rsUp (idsOf eouts))
      by (apply in_map_iff; exists (rsUp, rsm); auto).
    pose proof (atomic_rsUp_out_in_history Hrrs H2 H3 H4 _ H12 H13); clear H13.
    simpl in *.
    destruct H6 as [[? ?] ?]; simpl in *.

    intro Hx.
    eapply inside_child_in in Hx; [|apply H|eassumption].
    specialize (H15 ooidx); destruct H15; auto.
  Qed.

  Lemma rsUpMsgOutInv_no_rqDown:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall oidx rsum,
          In rsum eouts ->
          RsUpMsgOutInv (oindsOf hst) s2.(bst_orqs) oidx rsum ->
          forall ooidx orqdm,
            RqDownMsgTo ooidx orqdm ->
            In orqdm eouts ->
            ~ In ooidx (subtreeIndsOf dtr oidx).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    destruct rsum as [rsUp rsm].
    destruct orqdm as [orqDown orqm].
    disc_msg_case.
    pose proof (edgeDownTo_Some H _ H9).
    destruct H10 as [rqUp [rrsUp [pidx ?]]]; dest.
    assert (In orqDown (idsOf eouts))
      by (apply in_map_iff; exists (orqDown, orqm); auto).
    pose proof (atomic_down_out_in_history
                  Hrrs H2 H3 H4 _ H9 H12 H13); clear H13.
    simpl in *.
    destruct H6 as [[? ?] ?]; simpl in *.
    pose proof (steps_object_in_system H4 _ H14).
    destruct H16 as [pobj [? ?]].

    pose proof (atomic_messages_eouts_in msg_dec H2 H4).
    rewrite Forall_forall in H18.
    pose proof (H18 _ H5).
    pose proof (H18 _ H8).

    pose proof (downLockInv_ok H0 H (reachable_steps H3 H4)).
    good_locking_get pobj.

    intro Hx.
    destruct (eq_nat_dec ooidx oidx); subst.
    - eapply downLockInvORq_down_rqsQ_rsUp_False;
        try eapply H9; try eapply H13; try eassumption.
      + eapply rqsQ_length_ge_one; eauto.
      + eapply findQ_length_ge_one; eauto.
    - eapply inside_parent_in in Hx; try eassumption; [|apply Hrrs].
      specialize (H15 _ H14 Hx).
      eapply downLockInvORq_down_rqsQ_length_one_locked in H22;
        try eassumption.
      + destruct H22 as [rqid [? ?]].
        red in H15.
        destruct ((bst_orqs s2)@[obj_idx pobj]); simpl in *; [congruence|discriminate].
      + eapply rqsQ_length_ge_one; eauto.
  Qed.

  Lemma rsUpMsgOutInv_no_rsUp:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        forall oidx rsum,
          In rsum eouts ->
          RsUpMsgOutInv (oindsOf hst) s2.(bst_orqs) oidx rsum ->
          forall ooidx opidx opobj orsum,
            parentIdxOf dtr ooidx = Some opidx ->
            In opobj sys.(sys_objs) ->
            opobj.(obj_idx) = opidx ->
            RsUpMsgFrom ooidx orsum ->
            In orsum eouts -> rsum <> orsum ->
            ~ In opidx (subtreeIndsOf dtr oidx).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    destruct rsum as [rsUp rsm].
    destruct orsum as [orsUp orsm].
    disc_msg_case.
    assert (In orsUp (idsOf eouts))
      by (apply in_map_iff; exists (orsUp, orsm); auto).
    pose proof (atomic_rsUp_out_in_history Hrrs H2 H3 H4 _ H13 H14); clear H14.
    simpl in *.
    destruct H6 as [[? ?] ?]; simpl in *.

    destruct (in_dec eq_nat_dec ooidx (subtreeIndsOf dtr oidx));
      [|eapply outside_parent_out; [apply H| |]; eassumption].

    pose proof (downLockInv_ok H0 H (reachable_steps H3 H4)).
    good_locking_get opobj.
    pose proof (atomic_messages_eouts_in msg_dec H2 H4).
    rewrite Forall_forall in H19.
    pose proof (H19 _ H5).
    pose proof (H19 _ H11).
    
    destruct (eq_nat_dec oidx ooidx); subst.
    - exfalso.
      disc_rule_conds.
      eapply downLockInvORq_rsUp_length_two_False in H18;
        try eassumption.
      eapply findQ_length_two; [|eapply H20|eapply H21].
      simpl; intro Hx; subst; auto.

    - destruct (in_dec eq_nat_dec (obj_idx opobj) (oindsOf hst)).
      + intro Hx.
        specialize (H16 _ i0 Hx); red in H16.
        eapply downLockInvORq_rsUp_length_one_locked in H18;
          try eassumption;
          [|eapply findQ_length_ge_one; eassumption].
        destruct H18 as [rqid ?]; dest.
        destruct ((bst_orqs s2)@[obj_idx opobj]); simpl in *;
          [congruence|discriminate].

      + exfalso.
        change orsUp with (idOf (orsUp, orsm)) in H13.
        pose proof (atomic_non_visiting_rsUp_one
                      Hrrs H2 H3 H4 _ _ n0 H7 H13 H11).
        assert (In rsUp (idsOf eouts))
          by (apply in_map_iff; exists (rsUp, rsm); auto).
        pose proof (atomic_rsUp_out_in_history
                      Hrrs H2 H3 H4 _ H14 H22); clear H22.
        apply H9 in H23.
        elim n.
        eapply subtreeIndsOf_In_each_other_eq;
          try eapply Hrrs; assumption.
  Qed.

  Ltac disc_rule_custom ::=
    try disc_footprints_ok;
    try disc_messages_out;
    try disc_msg_case.

  Lemma step_rqDown_rsUp_NoDup:
    forall oidx pidx pobj,
      parentIdxOf dtr oidx = Some pidx ->
      In pobj sys.(sys_objs) ->
      pobj.(obj_idx) = pidx ->
      forall st1 ridx rins routs st2,
        Reachable (steps step_m) sys st1 ->
        step_m sys st1 (RlblInt oidx ridx rins routs) st2 ->
        forall eouts,
          Forall (fun eout =>
                    exists oidx,
                      RqDownMsgTo oidx eout \/
                      RsUpMsgFrom oidx eout) eouts ->
          Forall (InMPI (bst_msgs st1)) eouts ->
          NoDup (idsOf eouts) ->
          Forall (fun rout =>
                    exists oidx,
                      RqDownMsgTo oidx rout \/
                      RsUpMsgFrom oidx rout) routs ->
          NoDup (idsOf (removeL (id_dec msg_dec) eouts rins ++ routs)).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    rewrite idsOf_app.
    apply NoDup_DisjList;
      [apply removeL_idsOf_NoDup; assumption
      |inv_step; apply H25|].

    apply (DisjList_false_spec eq_nat_dec).
    intros midx ? ?.
    apply removeL_idsOf_In in H11.
    apply in_map_iff in H11; destruct H11 as [[midx1 msg1] [? ?]].
    apply in_map_iff in H12; destruct H12 as [[midx2 msg2] [? ?]].
    simpl in *; subst.
    rewrite Forall_forall in H7; specialize (H7 _ H13).
    destruct H7 as [oidx1 ?].
    rewrite Forall_forall in H10; specialize (H10 _ H14).
    destruct H10 as [oidx2 ?].
    assert (In midx (idsOf routs))
      by (apply in_map with (f:= idOf) in H14; assumption).
    rewrite Forall_forall in H8.
    specialize (H8 _ H13).
    
    pose proof (footprints_ok H0 H5).
    pose proof (reachable_steps H5 (steps_singleton H6)).
    pose proof (downLockInv_ok H0 H H12); clear H12.
    
    destruct H4, H7; try (disc_rule_conds; solve_midx_false; fail).
    - (** Two RqDown messages in the same channel *)
      inv_step.
      good_rqrs_rule_get rule.
      good_rqrs_rule_cases rule.
      + disc_rule_conds.
      + disc_rule_conds.
      + disc_rule_conds; [solve_midx_false| |].
        * (* [RqUpDown] *)
          good_locking_get obj.
          mred; simpl in H24.
          eapply RqRsDownMatch_rq_rs in H30; [|eassumption].
          destruct H30 as [cidx [rsUp ?]]; dest.
          disc_rule_conds.
          eapply downLockInvORq_down_rqsQ_length_two_False.
          { eassumption. }
          { eapply H33. }
          { eassumption. }
          { solve_q.
            erewrite findQ_In_NoDup_enqMsgs; [|apply H29|eassumption].
            solve_q.
            rewrite filter_app; simpl.
            rewrite H7; simpl.
            rewrite app_length; simpl.
            apply rqsQ_length_ge_one in H8; [|assumption].
            unfold rqsQ in H8; simpl in H8.
            omega.
          }

        * (* [RqDownDown] *)
          good_locking_get obj.
          mred; simpl in H17.
          eapply RqRsDownMatch_rq_rs in H16; [|eassumption].
          destruct H16 as [cidx [rsUp ?]]; dest.
          disc_rule_conds.
          eapply downLockInvORq_down_rqsQ_length_two_False.
          { eassumption. }
          { eapply H24. }
          { eassumption. }
          { solve_q.
            erewrite findQ_In_NoDup_enqMsgs; [|apply H29|eassumption].
            apply parentIdxOf_not_eq in H24; [|apply Hrrs].
            solve_q.
            rewrite filter_app; simpl.
            rewrite H7; simpl.
            rewrite app_length; simpl.
            apply rqsQ_length_ge_one in H8; [|assumption].
            unfold rqsQ in H8; simpl in H8.
            omega.
          }
          
      + disc_rule_conds.
      + disc_rule_conds.
        good_locking_get obj.
        mred; simpl in H32.
        eapply RqRsDownMatch_rq_rs in H30; [|eassumption].
        destruct H30 as [cidx [rsUp ?]]; dest.
        disc_rule_conds.
        eapply downLockInvORq_down_rqsQ_length_two_False.
        { eassumption. }
        { eapply H33. }
        { eassumption. }
        { solve_q.
          erewrite findQ_In_NoDup_enqMsgs; [|apply H29|eassumption].
          apply parentIdxOf_not_eq in H33; [|apply Hrrs].
          solve_q.
          rewrite filter_app; simpl.
          rewrite H7; simpl.
          rewrite app_length; simpl.
          apply rqsQ_length_ge_one in H8; [|assumption].
          unfold rqsQ in H8; simpl in H8.
          omega.
        }
      
    - (** Two RsUp messages in the same channel *)
      inv_step.
      good_rqrs_rule_get rule.
      good_rqrs_rule_cases rule.
      + disc_rule_conds; solve_midx_false.
      + disc_rule_conds.
        good_locking_get pobj.
        eapply downLockInvORq_rsUp_length_two_False; try eassumption.
        solve_q.
        rewrite app_length; simpl.
        apply findQ_length_ge_one in H8.
        simpl in H8; omega.
      + disc_rule_conds;
          try (rewrite Forall_forall in H42;
               specialize (H42 _ H14); simpl in H42;
               rewrite H7 in H42; discriminate; fail).
      + good_footprint_get (obj_idx obj).
        disc_rule_conds; try (solve_midx_false; fail).
        good_locking_get pobj.
        eapply downLockInvORq_rsUp_length_two_False; try eassumption.
        solve_q.
        rewrite app_length; simpl.
        rewrite H39; solve_q.
        apply findQ_length_ge_one in H8.
        simpl in H8; omega.
      + disc_rule_conds.
        rewrite Forall_forall in H37.
        specialize (H37 _ H14); simpl in H37.
        rewrite H7 in H37; discriminate.
  Qed.

  Ltac inv_MsgOutsCases :=
    match goal with
    | [H: MsgOutsCases _ _ _ _ |- _] => inv H
    end;
    repeat
      match goal with
      | [H: SubList [_] _ |- _] => apply SubList_singleton_In in H
      | [H: In _ [_] |- _] => Common.dest_in
      | [H1: In _ ?eouts, H2: Forall _ ?eouts |- _] =>
        rewrite Forall_forall in H2;
        let oidx := fresh "oidx" in pose proof (H2 _ H1) as [oidx ?]
      | [H: RqDownMsgOutInv _ _ _ \/ RsUpMsgOutInv _ _ _ _ |- _] => destruct H
      | [H: RqUpMsgOutInv _ _ _ _ |- _] => red in H; dest
      | [H: RsDownMsgOutInv _ _ _ _ _ |- _] => red in H; dest
      | [H: RqDownMsgOutInv _ _ _ |- _] => red in H; dest
      | [H: RsUpMsgOutInv _ _ _ _ |- _] => red in H; dest
      | [H: RqUpMsgFrom _ _ |- _] => disc_rule_conds; solve_midx_false; fail
      | [H: RsDownMsgTo _ _ |- _] => disc_rule_conds; solve_midx_false; fail
      | [H: RqDownMsgTo _ _ |- _] => disc_rule_conds; solve_midx_false; fail
      | [H: RsUpMsgFrom _ _ |- _] => disc_rule_conds; solve_midx_false; fail
      end.

  (*! Move lemmas upward *)

  Lemma upLockedNew_UpLocked:
    forall orqs1 orqs2 oidx,
      UpLockedNew orqs1 orqs2 oidx ->
      UpLocked orqs2 oidx.
  Proof.
    unfold UpLockedNew, UpLocked; intros.
    destruct (orqs2@[oidx]); simpl in *; dest; auto.
  Qed.

  Lemma disjExceptUpLocked_history_add:
    forall oinds orqs1 orqs2 rcidx,
      DisjExceptUpLocked oinds orqs1 orqs2 rcidx ->
      forall oidx,
        ~ In oidx (subtreeIndsOf dtr rcidx) ->
        DisjExceptUpLocked (oidx :: oinds) orqs1 orqs2 rcidx.
  Proof.
    unfold DisjExceptUpLocked; intros.
    Common.dest_in; auto.
  Qed.

  Lemma disjExceptUpLocked_child:
    forall oinds orqs1 orqs2 oidx,
      DisjExceptUpLocked oinds orqs1 orqs2 oidx ->
      forall cidx rqid,
        parentIdxOf dtr cidx = Some oidx ->
        DisjExceptUpLocked (oidx :: oinds) orqs1 (orqs2 +[oidx <- rqid]) cidx.
  Proof.
    unfold DisjExceptUpLocked; intros.
    destruct (eq_nat_dec oidx oidx0); subst;
      [apply parent_not_in_subtree; [apply Hrrs|]; assumption|].
    destruct H1; [exfalso; auto|].
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
      forall cidx rqid,
        parentIdxOf dtr cidx = Some oidx ->
        UpLockCoverInv (oidx :: oinds) (orqs +[oidx <- rqid]) cidx.
  Proof.
    unfold UpLockCoverInv; intros.
    destruct (eq_nat_dec oidx oidx0); subst.
    - exfalso.
      eapply parent_not_in_subtree with (oidx:= cidx);
        [apply Hrrs|..]; eassumption.
    - destruct H2; [exfalso; auto|mred].
      apply subtreeIndsOf_child_SubList in H0; [|apply Hrrs].
      apply H0 in H1.
      specialize (H _ H1 H2 _ _ H3 H4 _ _ H5 H6 H7).
      apply (DisjList_cons_inv eq_nat_dec); auto.
      intro Hx.
      apply subtreeIndsOf_child_SubList in H5; [|apply Hrrs].
      apply H5 in Hx.
      eapply subtreeIndsOf_In_each_other_eq in Hx; try apply Hrrs; eauto.
  Qed.

  Section InternalStep.

    Variables (st0: MState oifc)
              (inits ins: list (Id Msg)) (hst: MHistory) (outs eouts: list (Id Msg))
              (oss: OStates oifc) (orqs: ORqs Msg) (msgs: MessagePool Msg)
              (obj: Object oifc) (rule: Rule oifc)
              (post: OState oifc) (porq: ORq Msg) (rins: list (Id Msg))
              (nost: OState oifc) (norq: ORq Msg) (routs: list (Id Msg)).

    Hypotheses
      (Hatm: Atomic msg_dec inits ins hst outs eouts)
      (Hrch: Reachable (steps step_m) sys st0)
      (Hsteps: steps step_m sys st0 hst {| bst_oss := oss;
                                           bst_orqs := orqs;
                                           bst_msgs := msgs |})
      (Hrins: rins <> nil)
      (Hosub: SubList rins eouts)
      (Hmoc: MsgOutsCases (oindsOf hst) st0.(bst_orqs) orqs eouts)
      (Hftinv: FootprintsOk dtr sys {| bst_oss := oss;
                                       bst_orqs := orqs;
                                       bst_msgs := msgs |})
      (Hdlinv: DownLockInv dtr sys {| bst_oss := oss;
                                      bst_orqs := orqs;
                                      bst_msgs := msgs |})
      (Hnodup:
         forall pobj,
           In pobj sys.(sys_objs) ->
           parentIdxOf dtr (obj_idx obj) = Some (obj_idx pobj) ->
           Forall (fun eout =>
                     exists oidx,
                       RqDownMsgTo oidx eout \/
                       RsUpMsgFrom oidx eout) eouts ->
           Forall (fun rout =>
                     exists oidx,
                       RqDownMsgTo oidx rout \/
                       RsUpMsgFrom oidx rout) routs ->
           NoDup (idsOf (removeL (id_dec msg_dec) eouts rins ++ routs))).

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

    Lemma step_msg_outs_ok_ImmDownRule:
      ImmDownRule dtr (obj_idx obj) rule ->
      MsgOutsCases (obj_idx obj :: oindsOf hst)
                   (bst_orqs st0) (orqs +[obj_idx obj <- norq])
                   (removeL (id_dec msg_dec) eouts rins ++ routs).
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      disc_rule_conds.
      replace (orqs+[obj_idx obj <- norq]) with orqs by meq.
      inv_MsgOutsCases.

      unfold removeOnce.
      destruct (id_dec msg_dec _ _); [clear e; simpl|exfalso; auto].
      eapply MsgOutsRsDown.
      red; repeat ssplit.
      - red; eauto.
      - red; intros; Common.dest_in; eauto.
        apply parent_not_in_subtree; [apply Hrrs|]; assumption.
      - disc_rule_conds.
        red; intros; Common.dest_in; [exfalso; disc_rule_conds|].
        apply (DisjList_cons_inv eq_nat_dec).
        + eapply H5; eauto.
        + intro Hx.
          apply subtreeIndsOf_child_SubList in H15; [|apply Hrrs].
          apply subtreeIndsOf_SubList in H7; [|apply Hrrs].
          apply H15, H7 in Hx.
          eapply parent_not_in_subtree; [apply Hrrs|..]; eauto.
      - red; intros; Common.dest_in; [right; red; mred|].
        specialize (H3 _ H11).
        left; eapply upLockedNew_UpLocked; eauto.
    Qed.

    Lemma step_msg_outs_ok_ImmUpRule:
      ImmUpRule dtr (obj_idx obj) rule ->
      MsgOutsCases (obj_idx obj :: oindsOf hst)
                   (bst_orqs st0) (orqs +[obj_idx obj <- norq])
                   (removeL (id_dec msg_dec) eouts rins ++ routs).
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      disc_rule_conds.
      replace (orqs+[obj_idx obj <- norq]) with orqs by meq.
      inv_MsgOutsCases.

      pose proof (edgeDownTo_Some H _ H11).
      destruct H12 as [rqUp [rsUp [pidx ?]]]; dest.
      disc_rule_conds.
      assert (In rqFrom (idsOf eouts))
        by (apply in_map_iff; exists (rqFrom, rqm); auto).
      pose proof (atomic_down_out_in_history
                    Hrrs Hatm Hrch Hsteps _ H11 H14 H13); clear H13.

      eapply MsgOutsRqDownRsUp.
      - (** [NoDup eouts] *)
        pose proof (steps_object_in_system Hsteps _ H15).
        destruct H13 as [pobj [? ?]]; subst.
        eapply Hnodup with (pobj0:= pobj).
        + assumption.
        + reflexivity.
        + eapply rqDown_rsUp_inv_msg.
          rewrite Forall_forall; eassumption.
        + repeat constructor.
          exists (obj_idx obj); right.
          red; auto.

      - (** Invariant for each message *)
        apply Forall_app.
        + (* For the others except (rqFrom, rqm) *)
          apply Forall_forall.
          intros [midx msg] ?.
          apply removeOnce_In_NoDup in H13;
            [|apply idsOf_NoDup; assumption]; dest.
          pose proof (H3 _ H16).
          destruct H18 as [oidx ?].
          destruct H18.
          * (* RqDown *)
            exists oidx; left.
            destruct H18.
            split; [assumption|].
            red in H19.
            red; simpl.
            apply (DisjList_cons_inv eq_nat_dec); [assumption|].
            eapply rqDownMsgOutInv_no_rqDown
              with (oidx := oidx) (rqdm := (midx, msg))
                   (ooidx := obj_idx obj) (orqdm := (rqFrom, rqm));
              try eassumption.
            { split; assumption. }
            { split; assumption. }
            { congruence. }
          * (* RsUp *)
            exists oidx; right.
            destruct H18.
            split; [assumption|].
            red; simpl; intros.
            destruct H20; [subst|auto].
            red; mred.
        + (* For the new output *)
          repeat constructor.
          exists (obj_idx obj); right.
          split; [red; auto|].
          red; simpl; intros.
          destruct H13.
          * subst; red; mred.
          * specialize (H10 oidx); destruct H10; exfalso; auto.

      - (** [DownLockRootInv] *)
        intros.
        assert (DownLockRoot (oindsOf hst) orqs roidx rorq rrqid rcidx).
        { red in H13; dest.
          destruct H13; subst; [exfalso; red in H18; mred|].
          red; repeat ssplit; assumption.
        }
        specialize (H5 _ _ _ _ H16); clear H13 H16.
        specialize (H3 _ Hosub).
        destruct H3 as [oidx ?].
        destruct H3; [|destruct H3; disc_rule_conds].
        destruct H3.
        red in H5; dest.
        pose proof H5.
        red in H20; rewrite Forall_forall in H20.
        specialize (H20 _ Hosub).
        red in H20; dest.
        specialize (H20 _ H3); dest.
        disc_rule_conds.
        
        red; repeat ssplit.
        + (* [OutsInRoot] *)
          apply Forall_app.
          * apply forall_removeOnce; assumption.
          * constructor; [|constructor].
            split; [red; intros; disc_rule_conds|].
            red; intros; split; disc_rule_conds.
        + (* [DisjExceptUpLocked] *)
          disc_rule_conds.
          apply disjExceptUpLocked_history_add; auto.
        + (* [UpLockCoverInv] *)
          red; intros; Common.dest_in; [exfalso; auto|].
          apply (DisjList_cons_inv eq_nat_dec); [eapply H18; eauto|].
          intro Hx; elim H22.
          apply subtreeIndsOf_child_SubList in H27; [|apply Hrrs].
          apply H27 in Hx.
          apply subtreeIndsOf_SubList in H23; [|apply Hrrs].
          apply H23; assumption.
        + (* [DownLocksCoverInv] *)
          red; simpl; intros.
          destruct H23; [subst; red in H26; mred|].
          red; intros.
          red; simpl.
          apply (DisjList_cons_inv eq_nat_dec); [eapply H19; eauto|].
          intro Hx.
          specialize (H19 _ _ H23 H24 H25 H26 _ _ _ H27 H28 H29 H30 H31).
          eapply DisjList_In_2 in H15; [|eapply H19].
          eapply inside_child_outside_parent_case in Hx;
            try eassumption; try apply Hrrs; subst.
          disc_rule_conds.
          pose proof (steps_object_in_system Hsteps _ H23).
          destruct H27 as [dobj [? ?]]; subst.
          good_locking_get dobj; mred.
          red in H26, H28.
          destruct (orqs@[obj_idx dobj]) as [dorq|]; simpl in *; auto.
          rewrite H26 in H28.
          specialize (H28 _ H14).
          destruct H28 as [rdown [rsUp ?]]; dest.
          disc_rule_conds.
          destruct (in_dec eq_nat_dec rsUp _); [auto|].
          red in H32; dest.
          eapply rqsQ_length_zero_False; eauto.
    Qed.
    
    Lemma step_msg_outs_ok_RsDownRqDownRule:
      RsDownRqDownRule dtr sys (obj_idx obj) rule ->
      MsgOutsCases (obj_idx obj :: oindsOf hst)
                   st0.(bst_orqs) (orqs +[obj_idx obj <- norq])
                                  (removeL (id_dec msg_dec) eouts rins ++ routs).
    Proof.
      destruct Hrrs as [? [? ?]]; intros.
      disc_rule_conds.
      inv_MsgOutsCases.
      unfold removeOnce in *.
      destruct (id_dec msg_dec _ _); [clear e; simpl|exfalso; auto].
      simpl in *.
      disc_rule_conds.

      eapply MsgOutsRqDownRsUp; [apply HmoutsV|..].
        
      - (** Invariant for each message *)
        apply Forall_forall.
        intros [rqTo rqm] ?.
        assert (In rqTo (idsOf routs))
          by (apply in_map_iff; exists (rqTo, rqm); auto).
        eapply RqRsDownMatch_rq_rs in H10; [|eassumption].
        destruct H10 as [cidx [rsUp ?]]; dest.
        rewrite Forall_forall in H15.
        pose proof (H15 _ H14); simpl in H24.
        disc_rule_conds.
        exists cidx; left.
        split; [red; auto|].
        red; simpl.
        apply (DisjList_cons_inv eq_nat_dec);
          [|apply parent_not_in_subtree; [apply Hrrs|auto]].
        destruct (in_dec eq_nat_dec (obj_idx obj) (oindsOf hst)).
        + eapply H13; eauto.
          * eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption].
          * intro Hx; subst.
            disc_rule_conds; auto.
        + eapply atomic_separation_ok in n; eauto.
          destruct n.
          1: {
            exfalso; destruct H27 as [rcidx [? ?]].
            pose proof (edgeDownTo_Some H _ H19).
            destruct H29 as [rqUp [rrsUp [pidx ?]]]; dest.
            disc_rule_conds.
            pose proof Hatm.
            eapply atomic_down_out_in_history with (down:= rsFrom) in H19;
              eauto; [|left; reflexivity].
            apply H28 in H19.
            eapply parent_parent_in_False with (oidx2:= obj_idx obj);
              try apply Hrrs; eassumption.
          }
          eapply DisjList_comm, DisjList_SubList.
          * eapply subtreeIndsOf_child_SubList; [apply Hrrs|eassumption].
          * apply DisjList_comm; assumption.

      - (** [DownLockRootInv] *)
        intros; red in H14; dest.
        destruct (eq_nat_dec roidx (obj_idx obj)); [subst; clear H14|].
        2: {
          exfalso; destruct H14; [auto|].
          specialize (H11 _ H14); destruct H11.
          { red in H11, H16; mred.
            destruct (orqs@[roidx]); simpl in *; auto.
          }
          { red in H11, H18; mred.
            destruct (orqs@[roidx]); simpl in *; congruence.
          }
        }

        red in H18; repeat (simpl in H18; mred).
        clear H16.
        red; repeat ssplit.
        + (* [OutsInRoot] *)
          apply Forall_forall.
          intros [rqTo rqm] ?.
          assert (In rqTo (idsOf routs))
            by (apply in_map_iff; exists (rqTo, rqm); auto).
          eapply RqRsDownMatch_rq_rs in H10; [|eassumption].
          destruct H10 as [cidx [rsUp ?]]; dest.
          rewrite Forall_forall in H15.
          pose proof (H15 _ H14); simpl in H28.
          split.
          * red; intros; disc_rule_conds.
            split.
            { apply subtreeIndsOf_child_in; [apply Hrrs|assumption]. }
            { eapply subtreeIndsOf_other_child_not_in; [apply Hrrs|..]; eauto. }
          * red; intros; disc_rule_conds.

        + (* [DisjExceptUpLocked] *)
          eapply disjExceptUpLocked_child; eauto.
        + (* [UpLockCoverInv] *)
          eapply upLockCoverInv_child; eauto.

        + (* [DownLocksCoverInv] *)
          destruct (in_dec eq_nat_dec (obj_idx obj) (oindsOf hst)).
          * red; intros.
            red in H13.
            assert (In (obj_idx obj) (subtreeIndsOf dtr (obj_idx obj))).
            { eapply parent_subtreeIndsOf_self_in; [apply Hrrs|eassumption]. }
            specialize (H13 (obj_idx obj) H24 i _ _ Hporq H17); clear H24.

            destruct (eq_nat_dec oidx (obj_idx obj)); subst.
            { clear H14 H16.
              red in H22; repeat (simpl in H22; mred).
              red; intros.
              apply (DisjList_cons_inv eq_nat_dec).
              { rewrite H25 in H27.
                specialize (H13 _ _ H14 H22 H27).
                assumption.
              }
              { eapply parent_not_in_subtree; [apply Hrrs|assumption]. }
            }
            { exfalso; destruct H14; [auto|].
              apply subtreeIndsOf_composed in H16; [|apply Hrrs].
              destruct H16; [auto|].
              destruct H16 as [ocidx ?]; dest.
              pose proof (parentIdxOf_Some H _ H16).
              destruct H27 as [orqUp [orsUp [odown ?]]]; dest.
              assert (odown <> rqi_midx_rsb rqi1).
              { intro Hx; subst; disc_rule_conds; auto. }
              specialize (H13 _ _ H16 H29 H30).
              destruct (H13 oidx); auto.
            }

          * eapply atomic_separation_ok in n; eauto.
            destruct n.
            1: {
              exfalso; destruct H14 as [ccidx [? ?]].
              pose proof (edgeDownTo_Some H _ H19).
              destruct H18 as [rqUp [rrsUp [pidx ?]]]; dest.
              disc_rule_conds.
              pose proof Hatm.
              eapply atomic_down_out_in_history with (down:= rsFrom) in H20;
                eauto; [|left; reflexivity].
              apply H16 in H20.
              eapply parent_parent_in_False with (oidx2:= obj_idx obj);
                try apply Hrrs; eassumption.
            }

            red; intros.
            destruct (eq_nat_dec oidx (obj_idx obj)); subst.
            { clear H16 H18.
              red in H24; repeat (simpl in H24; mred).
              red; intros.
              apply (DisjList_cons_inv eq_nat_dec).
              { eapply DisjList_comm, DisjList_SubList.
                { eapply subtreeIndsOf_child_SubList; [apply Hrrs|eassumption]. }
                { apply DisjList_comm; assumption. }
              }
              { eapply parent_not_in_subtree; [apply Hrrs|assumption]. }
            }
            { exfalso.
              destruct H16; subst; [auto|].
              destruct (H14 oidx); auto.
            }
    Qed.

    Lemma step_msg_outs_ok_RqFwdRule:
      RqFwdRule dtr sys (obj_idx obj) rule ->
      MsgOutsCases (obj_idx obj :: oindsOf hst)
                   (bst_orqs st0) (orqs +[obj_idx obj <- norq])
                   (removeL (id_dec msg_dec) eouts rins ++ routs).
    Proof.
      (* destruct Hrrs as [? [? ?]]; intros. *)
      (* disc_rule_conds. *)

      (* - inv_MsgOutsCases. *)
      (*   unfold removeOnce. *)
      (*   destruct (id_dec msg_dec _ _); [clear e; simpl|exfalso; auto]. *)
      (*   eapply MsgOutsRqUp. *)
      (*   + split; [red; eauto|]. *)
      (*     red; intros; mred. *)
      (*     clear H17; destruct H23; subst; [left; reflexivity|]. *)
      (*     admit. *)
      (*   + admit. *)

      (*     inv_MsgOutsCases. *)
      (*     pose proof (edgeDownTo_Some H _ H2). *)
      (*     destruct H19 as [rqUp [rsUp [pidx ?]]]; dest. *)
      (*     disc_rule_conds. *)
      (*     assert (In rqFrom (idsOf eouts)) *)
      (*       by (apply in_map_iff; exists (rqFrom, rqi_msg rqi); auto). *)
      (*     pose proof (atomic_down_out_in_history *)
      (*                   Hrrs Hatm Hrch Hsteps _ H2 H22 H21); clear H21. *)

      (*     eapply MsgOutsRqDownRsUp. *)
      (* - pose proof (steps_object_in_system Hsteps _ H23). *)
      (*   destruct H21 as [pobj [? ?]]; subst. *)
      (*   eapply Hnodup with (pobj0:= pobj). *)
      (*   + assumption. *)
      (*   + reflexivity. *)
      (*   + eapply rqDown_rsUp_inv_msg. *)
      (*     rewrite Forall_forall; eassumption. *)
      (*   + apply Forall_forall. *)
      (*     intros [rqDown rqm] ?. *)
      (*     rewrite Forall_forall in H20; specialize (H20 _ H24). *)
      (*     apply in_map with (f:= idOf) in H24; simpl in H24. *)
      (*     eapply RqRsDownMatch_rq_rs in H4; [|eassumption]. *)
      (*     destruct H4 as [cidx [rsUp ?]]; dest. *)
      (*     exists cidx; left. *)
      (*     red; auto. *)

      (* - apply Forall_app. *)
      (*   + apply Forall_forall. *)
      (*     intros [midx msg] ?. *)
      (*     apply removeOnce_In_NoDup in H21; *)
      (*       [|apply idsOf_NoDup; assumption]; dest. *)

      (*     pose proof (H7 _ H24). *)
      (*     destruct H25 as [oidx ?]. *)
      (*     destruct H25. *)
      (*     * (* RqDown *) *)
      (*       exists oidx; left. *)
      (*       destruct H25. *)
      (*       split; [assumption|]. *)
      (*       red in H26. *)
      (*       red; simpl. *)
      (*       apply (DisjList_cons_inv eq_nat_dec); [assumption|]. *)

      (*       eapply rqDownMsgOutInv_no_rqDown *)
      (*         with (oidx := oidx) (rqdm := (midx, msg)) *)
      (*              (ooidx := obj_idx obj) (orqdm := (rqFrom, rqi_msg rqi)); *)
      (*         try eassumption. *)
      (*       { split; assumption. } *)
      (*       { split; assumption. } *)
      (*       { congruence. } *)
      (*     * (* RsUp *) *)
      (*       exists oidx; right. *)
      (*       destruct H25. *)
      (*       split; [assumption|]. *)

      (*       red; simpl; intros. *)
      (*       destruct (eq_nat_dec (obj_idx obj) oidx0). *)
      (*       { subst; exfalso. *)
      (*         eapply rsUpMsgOutInv_no_rqDown *)
      (*           with (oidx := oidx) (rsum := (midx, msg)) *)
      (*                (ooidx := obj_idx obj) (orqdm := (rqFrom, rqi_msg rqi)); *)
      (*           try eassumption. *)
      (*         { split; assumption. } *)
      (*         { split; assumption. } *)
      (*       } *)
      (*       { destruct H27; [exfalso; auto|]. *)
      (*         specialize (H26 _ H27 H28). *)
      (*         red; mred. *)
      (*       } *)

      (*   + apply Forall_forall. *)
      (*     intros [rqTo rqm] ?. *)
      (*     assert (In rqTo (idsOf routs)) *)
      (*       by (apply in_map_iff; exists (rqTo, rqm); auto). *)
      (*     eapply RqRsDownMatch_rq_rs in H4; [|eassumption]. *)
      (*     destruct H4 as [cidx [rsUp ?]]; dest. *)
      (*     rewrite Forall_forall in H20. *)
      (*     pose proof (H20 _ H21); simpl in H29. *)
      (*     exists cidx; left. *)
      (*     split; [red; auto|]. *)
      (*     red in H18; red; simpl. *)
      (*     apply (DisjList_cons_inv eq_nat_dec). *)
      (*     { apply DisjList_comm in H18. *)
      (*       eapply DisjList_comm, DisjList_SubList; *)
      (*         [|eassumption]. *)
      (*       eapply subtreeIndsOf_child_SubList; *)
      (*         [apply Hrrs|assumption]. *)
      (*     } *)
      (*     { apply parent_not_in_subtree; [apply Hrrs|auto]. } *)

      (* - red; simpl; intros. *)
      (*   destruct (eq_nat_dec (obj_idx obj) oidx). *)
      (*   + subst; mred. *)
      (*     red; intros. *)
      (*     red in H18; red; simpl. *)
      (*     apply (DisjList_cons_inv eq_nat_dec). *)
      (*     * eapply DisjList_comm in H18. *)
      (*       eapply DisjList_comm, DisjList_SubList; [|eassumption]. *)
      (*       apply subtreeIndsOf_child_SubList; *)
      (*         [apply Hrrs|assumption]. *)
      (*     * eapply parent_not_in_subtree; [apply Hrrs|auto]. *)
      (*   + destruct H21; [exfalso; auto|]. *)
      (*     mred; specialize (H11 _ _ _ H21 H24 H25). *)
      (*     red; intros. *)
      (*     specialize (H11 _ _ H26 H27 H28). *)
      (*     red in H11. *)
      (*     red; simpl; intros. *)
      (*     apply (DisjList_cons_inv eq_nat_dec); [assumption|]. *)
      (*     eapply DisjList_In_2 in H23; [|eapply H11]. *)
      (*     eapply outside_child_in in H23; try apply Hrrs; [|eassumption]. *)
      (*     destruct H23; [subst; exfalso|assumption]. *)
      (*     pose proof (steps_object_in_system Hsteps _ H21). *)
      (*     destruct H23 as [oobj [? ?]]; subst. *)
      (*     good_locking_get oobj. *)
      (*     red in H29; mred. *)

      (*     disc_rule_conds. *)
      (*     specialize (H29 _ H22). *)
      (*     destruct H29 as [down [rsUp ?]]; dest. *)
      (*     disc_rule_conds. *)
      (*     destruct (in_dec eq_nat_dec (rqi_midx_rsb rqi) _); [auto|]. *)
      (*     red in H29; dest. *)
      (*     eapply rqsQ_length_zero_False; eauto. *)
          
      (* - red; simpl; intros. *)
      (*   destruct (eq_nat_dec (obj_idx obj) roidx); *)
      (*     [subst; exfalso; mred; solve_midx_false|]. *)
      (*   destruct H21; [exfalso; auto|]. *)
      (*   mred. *)
      (*   specialize (H13 _ _ _ _ _ H21 H24 H25 H26 H27 H28); dest. *)
      (*   repeat ssplit; [assumption| |]. *)
      (*   + red in H29. *)
      (*     red; simpl. *)
      (*     apply (DisjList_cons_inv eq_nat_dec); [auto|]. *)
      (*     intro Hx. *)
      (*     eapply DisjList_In_2 in H23; [|apply H29]. *)
      (*     eapply inside_child_outside_parent_case in Hx; *)
      (*       try eassumption; try apply Hrrs; subst. *)
      (*     disc_rule_conds. *)

      (*     pose proof (steps_object_in_system Hsteps _ H21). *)
      (*     destruct H26 as [robj [? ?]]; subst. *)
      (*     good_locking_get robj; mred. *)
      (*     red in H27; mred. *)
      (*     specialize (H27 _ H22). *)
      (*     destruct H27 as [down [rsUp ?]]; dest. *)
      (*     disc_rule_conds. *)
      (*     destruct (in_dec eq_nat_dec (rqi_midx_rsb rqi) _); [auto|]. *)
      (*     red in H31; dest. *)
      (*     eapply rqsQ_length_zero_False; eauto. *)
      (*   + red; simpl; intros. *)
      (*     destruct (eq_nat_dec (obj_idx obj) sidx). *)
      (*     * subst; clear H31; mred. *)
      (*       pose proof (steps_object_in_system Hsteps _ H23). *)
      (*       destruct H31 as [pobj [? ?]]; subst. *)
      (*       good_locking_get pobj. *)
      (*       eapply downLockInvORq_down_rqsQ_length_one_locked in H32; *)
      (*         try eassumption; *)
      (*         [|eapply rqsQ_length_ge_one; *)
      (*           [eassumption|apply FirstMP_InMP; assumption]]. *)
      (*       destruct H32 as [prqid ?]; dest. *)
      (*       remember (orqs@[obj_idx pobj]) as pporq; apply eq_sym in Heqpporq. *)
      (*       destruct pporq as [pporq|]; [simpl in H32|discriminate]. *)
      (*       eapply inside_child_in; [apply Hrrs|eassumption|]. *)
      (*       eapply H30; eassumption. *)
      (*     * destruct H31; [exfalso; auto|]. *)
      (*       mred; eauto. *)
            
      (* - red; repeat (simpl; mred). *)
      (*   rewrite idsOf_app; simpl. *)
      (*   rewrite app_length; simpl. *)
      (*   unfold idsOf; rewrite map_length. *)
      (*   pose proof (removeOnce_length (id_dec msg_dec) _ _ Hosub); dest. *)
      (*   unfold Id in *; rewrite H24. *)
      (*   unfold DownLockNorm; repeat (simpl; mred). *)

      (*   red in H4; dest; rewrite <-H25. *)
      (*   rewrite downLocksNorm_orqs_add. *)
      (*   + assert (length (idsOf routs) > 0) *)
      (*       by (destruct (idsOf routs); [exfalso; auto|simpl; omega]). *)
      (*     red in H15. *)
      (*     unfold idsOf in H15; rewrite map_length in H15. *)
      (*     rewrite H15. *)
      (*     unfold idsOf in *. *)
      (*     omega. *)
      (*   + specialize (H7 _ Hosub). *)
      (*     destruct H7 as [oidx ?]. *)
      (*     destruct H7; [|destruct H7; disc_rule_conds]. *)
      (*     destruct H7; disc_rule_conds. *)
      (*     red in H18. *)
      (*     eapply DisjList_In_1. *)
      (*     * eassumption. *)
      (*     * apply rsEdgeUpFrom_subtreeIndsOf_self_in; [apply Hrrs|congruence]. *)
    Admitted.

    Lemma step_msg_outs_ok_RsBackRule:
      RsBackRule rule ->
      MsgOutsCases (obj_idx obj :: oindsOf hst)
                   (bst_orqs st0) (orqs +[obj_idx obj <- norq])
                   (removeL (id_dec msg_dec) eouts rins ++ routs).
    Proof.
      (* destruct Hrrs as [? [? ?]]; intros. *)
      (* good_footprint_get (obj_idx obj). *)
      (* disc_rule_conds. *)
      (* - (** [RsDownDown] *) *)
      (*   inv_MsgOutsCases. *)
      (*   disc_rule_conds. *)
      (*   destruct (id_dec msg_dec i i) as [_|]; [simpl|exfalso; auto]. *)

      (*   eapply MsgOutsRsDown. *)
      (*   + split; [red; simpl; eauto|]. *)
      (*     red; simpl. *)
      (*     apply (DisjList_cons_inv eq_nat_dec). *)
      (*     * red in H16; apply DisjList_comm in H16. *)
      (*       eapply DisjList_comm, DisjList_SubList; [|eassumption]. *)
      (*       apply subtreeIndsOf_child_SubList; [apply Hrrs|assumption]. *)
      (*     * apply parent_not_in_subtree; [apply Hrrs|assumption]. *)
      (*   + red; simpl; intros. *)
      (*     destruct H18; subst. *)
      (*     * red; repeat (simpl; mred). *)
      (*     * specialize (H15 _ H18). *)
      (*       red in H15; red. *)
      (*       repeat (simpl; mred). *)

      (* - (** [RsUpDown] *) *)
      (*   inv_MsgOutsCases. *)
      (*   + exfalso. *)
      (*     eapply SubList_singleton_NoDup in Hosub; *)
      (*       [|apply idsOf_NoDup, HminsV]. *)
      (*     destruct Hosub; [exfalso; auto|subst]. *)
      (*     rewrite <-H17 in H10. *)
      (*     eapply RqRsDownMatch_rs_rq in H10; [|left; reflexivity]. *)
      (*     destruct H10 as [cidx [down ?]]; dest. *)
      (*     disc_rule_conds. *)
      (*     solve_midx_false. *)

      (*   + pose proof (edgeDownTo_Some H _ H9). *)
      (*     destruct H18 as [rqUp [rsUp [pidx ?]]]; dest. *)
      (*     disc_rule_conds. *)
      (*     rewrite Forall_forall in H11. *)

      (*     (* Different proofs whether the object is part of the history or not *) *)
      (*     destruct (in_dec eq_nat_dec (obj_idx obj) (oindsOf hst)). *)
      (*     * (* If the object is in the history, we can use 1) [DownLockRootInv] *) *)
      (*       (*            * to say all downlocks are in the tree of the object and 2) the RsUp *) *)
      (*       (*            * invariants to say there are no downlocks in the tree. *) *)
      (*       (*            *) *)
      (*       specialize (H15 _ _ _ _ _ i Hporq H14 H5 H9 H19); dest. *)
      (*       specialize (H13 _ _ _ i Hporq H14). *)
      (*       assert (removeL (id_dec msg_dec) eouts rins = nil). *)
      (*       { eapply SubList_NoDup_length_eq_removeL_nil. *)
      (*         { assumption. } *)
      (*         { apply idsOf_NoDup, HminsV. } *)
      (*         { (* [length rins = length eouts] *) *)
      (*           (** FIXME: must use [downLocksNorm_rsUps] here, but it requires *) *)
      (*           (*                * strengthening the invariant about the RsDown-root to appear *) *)
      (*           (*                * at most once in the history. *) *)
      (*           (*                *) *)
      (*           admit. *)
      (*         } *)
      (*       } *)
      (*       rewrite H21; simpl; clear H21. *)
            
      (*       eapply MsgOutsRsDown. *)
      (*       { split; [red; eauto|]. *)
      (*         red; simpl. *)
      (*         apply (DisjList_cons_inv eq_nat_dec); [assumption|]. *)
      (*         apply parent_not_in_subtree; [apply Hrrs|assumption]. *)
      (*       } *)
      (*       { simpl; red; simpl; intros. *)
      (*         destruct (eq_nat_dec (obj_idx obj) oidx); *)
      (*           [subst; red; repeat (simpl; mred)|]. *)
      (*         destruct H21; [exfalso; auto|]. *)
      (*         eapply downLockCoverInv_DownLockInRoot_NoDownLock with (ridx:= obj_idx obj). *)
      (*         { auto. } *)
      (*         { eassumption. } *)
      (*         { apply eq_sym; eassumption. } *)
      (*         { intros [rrsUp rrsm] ?. *)
      (*           rewrite <-H17 in H10. *)
      (*           assert (In rrsUp (idsOf rins)) *)
      (*             by (apply in_map with (f:= idOf) in H22; assumption). *)
      (*           eapply RqRsDownMatch_rs_rq in H10; [|eassumption]; clear H23. *)
      (*           destruct H10 as [rcidx [rdown ?]]; dest. *)
      (*           apply Hosub in H22. *)
      (*           specialize (H11 _ H22). *)
      (*           destruct H11 as [cidx ?]. *)
      (*           destruct H11; [destruct H11; disc_rule_conds; solve_midx_false|]. *)
      (*           exists cidx. *)
      (*           apply rsUpMsgOutInv_orqs_downRq_remove; assumption. *)
      (*         } *)
      (*         { assumption. } *)
      (*         { apply downLockInRoot_orqs_downRq_remove; assumption. } *)
      (*       } *)

      (*     * (* When [~ In (obj_idx obj) (oindsOf hst)] *) *)
      (*       admit. *)

      (* - (** [RsUpUp] *) *)
      (*   inv_MsgOutsCases. *)
      (*   { exfalso. *)
      (*     eapply SubList_singleton_NoDup in Hosub; *)
      (*       [|apply idsOf_NoDup, HminsV]. *)
      (*     destruct Hosub; [exfalso; auto|subst]. *)
      (*     rewrite <-H17 in H5. *)
      (*     eapply RqRsDownMatch_rs_rq in H5; [|left; reflexivity]. *)
      (*     destruct H5 as [cidx [down ?]]; dest. *)
      (*     disc_rule_conds. *)
      (*     solve_midx_false. *)
      (*   } *)

      (*   pose proof (edgeDownTo_Some H _ H2). *)
      (*   destruct H15 as [rqUp [rsUp [pidx ?]]]; dest. *)
      (*   rewrite Forall_forall in H9. *)
      (*   disc_rule_conds. *)

      (*   (* Different proofs whether the object is part of the history or not *) *)
      (*   destruct (in_dec eq_nat_dec (obj_idx obj) (oindsOf hst)). *)
      (*   + (* Need to have just one child of the incoming RsUp messages. *) *)
      (*     assert (exists rsFrom rsfm, In (rsFrom, rsfm) rins). *)
      (*     { destruct rins as [|[rsFrom rsfm] ?]; [exfalso; auto|]. *)
      (*       do 2 eexists; left; reflexivity. *)
      (*     } *)
      (*     destruct H16 as [rsFrom [rsfm ?]]. *)
      (*     rewrite Forall_forall in H8. *)
      (*     specialize (H8 _ H16); simpl in H8. *)
      (*     assert (In rsFrom (idsOf rins)) *)
      (*       by (apply in_map with (f:= idOf) in H16; assumption). *)
      (*     rewrite <-H17 in H5. *)
      (*     eapply RqRsDownMatch_rs_rq in H5; [|eassumption]; clear H19. *)
      (*     destruct H5 as [ccidx [down ?]]; dest. *)
      (*     eapply Hosub in H16. *)
      (*     assert (In rsFrom (idsOf eouts)) *)
      (*       by (apply in_map with (f:= idOf) in H16; assumption). *)
      (*     pose proof (atomic_rsUp_out_in_history *)
      (*                   Hrrs Hatm Hrch Hsteps _ H21 H23); clear H23. *)

      (*     eapply MsgOutsRqDownRsUp. *)
      (*     * (* [NoDup] for [RsUpUp] *) *)
      (*       eapply Hnodup. *)
      (*       { admit. } *)
      (*       { admit. } *)
      (*       { eapply rqDown_rsUp_inv_msg. *)
      (*         rewrite Forall_forall; eassumption. *)
      (*       } *)
      (*       { repeat constructor. *)
      (*         exists (obj_idx obj); right. *)
      (*         red; auto. *)
      (*       } *)

      (*     * apply Forall_app. *)
      (*       { apply Forall_forall. *)
      (*         intros [midx msg] ?. *)
      (*         apply removeL_In_NoDup in H23; [|apply idsOf_NoDup; assumption]; dest. *)
      (*         pose proof (H9 _ H25). *)
      (*         destruct H26 as [oidx ?]; destruct H26. *)
      (*         { exists oidx; left. *)
      (*           destruct H26. *)
      (*           split; [assumption|]. *)
      (*           red; simpl. *)
      (*           apply (DisjList_cons_inv eq_nat_dec); [auto|]. *)
      (*           eapply rqDownMsgOutInv_no_rsUp with (orsum := (rsFrom, rsfm)); *)
      (*             try eassumption. *)
      (*           { split; assumption. } *)
      (*           { reflexivity. } *)
      (*           { red; auto. } *)
      (*         } *)
      (*         { exists oidx; right. *)
      (*           destruct H26. *)
      (*           split; [assumption|]. *)
      (*           red; simpl; intros. *)
      (*           destruct (eq_nat_dec (obj_idx obj) oidx0); *)
      (*             [subst; red; repeat (simpl; mred)|]. *)
      (*           destruct H28; [exfalso; auto|]. *)
      (*           red; mred. *)
      (*           eapply H27; eauto. *)
      (*         } *)
      (*       } *)
      (*       { repeat constructor. *)
      (*         exists (obj_idx obj); right. *)
      (*         split; [red; auto|]. *)
      (*         red; simpl; intros. *)
      (*         destruct (eq_nat_dec (obj_idx obj) oidx); *)
      (*           [subst; red; repeat (simpl; mred)|]. *)
      (*         destruct H23; [exfalso; auto|]. *)
      (*         red; mred. *)
      (*         apply subtreeIndsOf_composed in H25; [|apply Hrrs]. *)
      (*         destruct H25; [exfalso; auto|]. *)
      (*         destruct H25 as [cidx [? ?]]. *)
      (*         pose proof (parentIdxOf_Some H _ H25). *)
      (*         destruct H27 as [crqUp [crsUp [cdown ?]]]; dest. *)
      (*         destruct (in_dec eq_nat_dec crsUp rqi.(rqi_minds_rss)). *)
      (*         { rewrite <-H17 in i0. *)
      (*           apply in_map_iff in i0. *)
      (*           destruct i0 as [[crsUp' crsm] [? ?]]; simpl in *; subst. *)
      (*           apply Hosub in H31. *)
      (*           specialize (H9 _ H31). *)
      (*           destruct H9 as [rcidx ?]. *)
      (*           destruct H9; [destruct H9; disc_rule_conds; solve_midx_false|]. *)
      (*           destruct H9; disc_rule_conds. *)
      (*           specialize (H30 _ H23 H26). *)
      (*           red in H30; destruct (orqs@[oidx]); auto. *)
      (*         } *)
      (*         { specialize (H10 _ _ _ i Hporq H14). *)
      (*           red in H10. *)
      (*           specialize (H10 _ _ H25 H28 n0 oidx). *)
      (*           exfalso; destruct H10; eauto. *)
      (*         } *)
      (*       } *)

      (*     * red; simpl; intros. *)
      (*       destruct (eq_nat_dec (obj_idx obj) oidx); *)
      (*         [subst; red; repeat (simpl; mred)|]. *)
      (*       destruct H23; [exfalso; auto|]. *)
      (*       mred; red; intros. *)
      (*       red; simpl; intros. *)
      (*       apply (DisjList_cons_inv eq_nat_dec); [eapply H10; eauto|]. *)
      (*       specialize (H10 _ _ _ H23 H25 H26). *)
      (*       specialize (H10 _ _ H27 H28 H29). *)
      (*       eapply outside_parent_out; [apply Hrrs| |eassumption]. *)
      (*       eapply DisjList_In_2; eassumption. *)

      (*     * red; simpl; intros. *)
      (*       destruct (eq_nat_dec (obj_idx obj) roidx); [subst; mred|]. *)
      (*       destruct H23; [exfalso; auto|]. *)
      (*       mred. *)
      (*       specialize (H11 _ _ _ _ _ H23 H25 H26 H27 H28 H29); dest. *)
      (*       repeat split; [assumption| |]. *)
      (*       { red; simpl. *)
      (*         apply (DisjList_cons_inv eq_nat_dec); [auto|]. *)
      (*         eapply outside_parent_out; [apply Hrrs| |eassumption]. *)
      (*         eapply DisjList_In_2; eassumption. *)
      (*       } *)
      (*       { red; simpl; intros. *)
      (*         destruct (eq_nat_dec (obj_idx obj) sidx); [subst; mred|]. *)
      (*         destruct H32; [exfalso; auto|]. *)
      (*         mred; eauto. *)
      (*       } *)

      (*     * red; repeat (simpl; mred). *)
      (*       rewrite idsOf_app, app_length; simpl. *)
      (*       unfold DownLockNorm; repeat (simpl; mred). *)
      (*       (* [MsgOutsNormInv] for [RsUpUp] *) *)
      (*       admit. *)

      (*   + (* When [~ In (obj_idx obj) (oindsOf hst)] *) *)
      (*     admit. *)
          
    Admitted.
    
  End InternalStep.
  
  Lemma atomic_msg_outs_ok:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall s1 s2,
        Reachable (steps step_m) sys s1 ->
        steps step_m sys s1 hst s2 ->
        MsgOutsCases (oindsOf hst) s1.(bst_orqs) s2.(bst_orqs) eouts.
  Proof.
    destruct Hrrs as [? [? ?]].
    induction 1; simpl; intros; subst;
      [inv_steps; eapply step_msg_outs_ok; eauto|].

    inv_steps.
    specialize (IHAtomic _ _ H8 H10).

    assert (Reachable (steps step_m) sys st2) by eauto.
    pose proof (footprints_ok H0 H5) as Hftinv.
    pose proof (downLockInv_ok H0 H H5) as Hdlinv.
    assert (forall pidx pobj,
               parentIdxOf dtr oidx = Some pidx ->
               In pobj (sys_objs sys) ->
               obj_idx pobj = pidx ->
               Forall (fun eout =>
                         exists oidx,
                           RqDownMsgTo oidx eout \/
                           RsUpMsgFrom oidx eout) eouts ->
               Forall (fun rout =>
                         exists oidx,
                           RqDownMsgTo oidx rout \/
                           RsUpMsgFrom oidx rout) routs ->
               NoDup (idsOf (removeL (id_dec msg_dec) eouts rins ++ routs)))
      as Hndinv.
    { intros; eapply step_rqDown_rsUp_NoDup; eauto.
      { eapply (atomic_messages_eouts_in msg_dec) in H2; [|eassumption].
        simpl in H2; assumption.
      }
      { eapply msgOutsCases_NoDup; eassumption. }
    }
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
        Atomic msg_dec inits ins hst outs eouts ->
        forall st1 st2,
          Reachable (steps step_m) sys st1 ->
          steps step_m sys st1 hst st2 ->
          DisjList (oindsOf hst) (subtreeIndsOf dtr oidx).
  Proof.
    destruct Hrrs as [? [? ?]]; intros.
    eapply atomic_msg_outs_ok in H4; eauto.
    inv H4.
    - exfalso.
      Common.dest_in.
      destruct H7.
      repeat disc_msg_case.
      solve_midx_false.
    - exfalso.
      Common.dest_in.
      destruct H7.
      repeat disc_msg_case.
      rewrite H2 in H3; discriminate.
    - rewrite Forall_forall in H8.
      specialize (H8 _ H3).
      destruct H8 as [doidx ?].
      destruct H4.
      + destruct H4.
        repeat disc_msg_case.
        disc_rule_conds.
      + exfalso.
        destruct H4.
        repeat disc_msg_case.
        solve_midx_false.
  Qed.

  Corollary atomic_rsDown_covers:
    forall oidx rsDown,
      RsDownMsgTo oidx rsDown ->
      forall inits ins hst outs eouts,
        In rsDown eouts ->
        Atomic msg_dec inits ins hst outs eouts ->
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
    - exfalso.
      Common.dest_in.
      destruct H9.
      repeat disc_msg_case.
      solve_midx_false.
    - Common.dest_in.
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

Close Scope list.
Close Scope fmap.

