Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvMsg.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section UpLockInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypotheses (Hrr: GoodRqRsSys dtr sys)
             (Hsd: RqRsDTree dtr sys).

  Section OnMState.
    Variables (orqs: ORqs Msg)
              (msgs: MessagePool Msg).

    Definition OLockedTo (oidx: IdxT) (rsbTo: IdxT) :=
      orqs@[oidx] >>=[False]
          (fun orq =>
             exists rqi,
               (orq@[upRq] = Some rqi \/ orq@[downRq] = Some rqi) /\
               rqi.(rqi_midx_rsb) = rsbTo).

    Definition ONoSameLockTo (oidx: IdxT) (rsbTo: IdxT) :=
      orqs@[oidx] >>=[True]
          (fun orq =>
             match orq@[upRq], orq@[downRq] with
             | Some rqiu, Some rqid =>
               rqiu.(rqi_midx_rsb) <> rsbTo \/ rqid.(rqi_midx_rsb) <> rsbTo
             | _, _ => True
             end).

    Definition OUpLockFree (oidx: IdxT) :=
      orqs@[oidx] >>=[True] (fun orq => UpLockFreeORq orq).

    Definition ONoLockTo (oidx: IdxT) (rsbTo: IdxT) :=
      orqs@[oidx] >>=[True]
          (fun orq =>
             match orq@[upRq] with
             | Some rqi => rqi.(rqi_midx_rsb) <> rsbTo
             | None => True
             end /\
             match orq@[downRq] with
             | Some rqi => rqi.(rqi_midx_rsb) <> rsbTo
             | None => True
             end).

    Definition UpLockFreeInv (oidx: IdxT) :=
      parentIdxOf dtr oidx = None \/
      exists rqUp down pidx,
        rqEdgeUpFrom dtr oidx = Some rqUp /\
        edgeDownTo dtr oidx = Some down /\
        parentIdxOf dtr oidx = Some pidx /\
        findQ rqUp msgs = nil /\
        rssQ msgs down = nil /\
        ONoLockTo pidx down.
    
    Definition UpLockedInv (oidx: IdxT) :=
      exists rqUp down pidx,
        rqEdgeUpFrom dtr oidx = Some rqUp /\
        edgeDownTo dtr oidx = Some down /\
        parentIdxOf dtr oidx = Some pidx /\
        length (findQ rqUp msgs) <= 1 /\
        length (rssQ msgs down) <= 1 /\
        ONoSameLockTo pidx down /\
        xor3 (length (findQ rqUp msgs) = 1)
             (length (rssQ msgs down) = 1)
             (OLockedTo pidx down).

    Definition UpLockInvORq (oidx: IdxT) (orq: ORq Msg) :=
      match orq@[upRq] with
      | Some _ => UpLockedInv oidx
      | None => UpLockFreeInv oidx
      end.

    Definition UpLockInvMO :=
      forall oidx,
        In oidx (map (@obj_idx _) sys.(sys_objs)) ->
        let orq := orqs@[oidx] >>=[[]] (fun orq => orq) in
        UpLockInvORq oidx orq.

  End OnMState.
  
  Definition UpLockInv (st: MState oifc) :=
    UpLockInvMO st.(bst_orqs) st.(bst_msgs).

  Lemma upLockInv_init:
    InvInit sys UpLockInv.
  Proof.
    intros; do 3 red; cbn.
    intros; cbn.
    red.
    remember (parentIdxOf dtr oidx) as opidx.
    destruct opidx as [pidx|]; [right|left; reflexivity].
    pose proof (eq_sym Heqopidx).
    eapply parentIdxOf_Some in H0; [|eassumption].
    destruct H0 as [rqUp [rsUp [down ?]]]; dest.
    do 3 eexists; repeat split; try eassumption.
  Qed.

  Lemma ONoLockTo_not_OLockedTo:
    forall orqs oidx rsbTo,
      ONoLockTo orqs oidx rsbTo -> ~ OLockedTo orqs oidx rsbTo.
  Proof.
    unfold ONoLockTo, OLockedTo; intros.
    intro Hx.
    destruct (orqs@[oidx]); simpl in *; auto; dest.
    destruct H1.
    - rewrite H1 in H; auto.
    - rewrite H1 in H0; auto.
  Qed.

  Lemma not_ONoLockTo_OLockedTo:
    forall orqs oidx rsbTo,
      ~ OLockedTo orqs oidx rsbTo -> ONoLockTo orqs oidx rsbTo.
  Proof.
    unfold ONoLockTo, OLockedTo; intros.
    destruct (orqs@[oidx]); simpl in *; auto.
    split.
    - destruct (o@[upRq]); auto.
      intro Hx; elim H.
      eexists; split; eauto.
    - destruct (o@[downRq]); auto.
      intro Hx; elim H.
      eexists; split; eauto.
  Qed.

  Lemma ONoLockTo_ONoSameLockTo:
    forall orqs oidx rsbTo,
      ONoLockTo orqs oidx rsbTo -> ONoSameLockTo orqs oidx rsbTo.
  Proof.
    unfold ONoLockTo, ONoSameLockTo; intros.
    destruct (orqs@[oidx]) as [orq|]; simpl in *; auto.
    destruct (orq@[upRq]) as [rqiu|]; simpl in *; auto.
    dest.
    destruct (orq@[downRq]) as [rqid|]; simpl in *; auto.
  Qed.

  Lemma OLockedTo_orqs_preserved:
    forall orqs1 orqs2 oidx rsbTo,
      OLockedTo orqs1 oidx rsbTo ->
      orqs1@[oidx] = orqs2@[oidx] ->
      OLockedTo orqs2 oidx rsbTo.
  Proof.
    unfold OLockedTo; intros.
    rewrite <-H0; assumption.
  Qed.

  Lemma upLockedInv_msgs_preserved:
    forall orqs msgs1 msgs2 oidx,
      UpLockedInv orqs msgs1 oidx ->
      (match rqEdgeUpFrom dtr oidx with
       | Some rqUp => findQ rqUp msgs1 = findQ rqUp msgs2
       | None => False
       end) ->
      (match edgeDownTo dtr oidx with
       | Some down => rssQ msgs1 down = rssQ msgs2 down
       | None => False
       end) ->
      UpLockedInv orqs msgs2 oidx.
  Proof.
    unfold UpLockedInv; simpl; intros.
    destruct H as [rqUp [down [pidx ?]]]; dest.
    rewrite H in H0.
    rewrite H2 in H1.
    exists rqUp, down, pidx.
    rewrite <-H0, <-H1.
    repeat split; try assumption.
  Qed.

  Corollary upLockedInv_disj_enqMsgs_preserved:
    forall orqs msgs emsgs oidx,
      UpLockedInv orqs msgs oidx ->
      DisjList (idsOf emsgs) (sys_minds sys) ->
      UpLockedInv orqs (enqMsgs emsgs msgs) oidx.
  Proof.
    intros.
    eapply upLockedInv_msgs_preserved; eauto.
    - destruct H as [rqUp [down [pidx ?]]]; dest.
      rewrite H.
      rewrite findQ_not_In_enqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_rqEdgeUpFrom_sys_minds; eauto.
    - destruct H as [rqUp [down [pidx ?]]]; dest.
      rewrite H1.
      unfold rssQ.
      rewrite findQ_not_In_enqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
  Qed.

  Corollary upLockedInv_disj_deqMsgs_preserved:
    forall orqs msgs eminds oidx,
      UpLockedInv orqs msgs oidx ->
      DisjList eminds (sys_minds sys) ->
      UpLockedInv orqs (deqMsgs eminds msgs) oidx.
  Proof.
    intros.
    eapply upLockedInv_msgs_preserved; eauto.
    - destruct H as [rqUp [down [pidx ?]]]; dest.
      rewrite H.
      rewrite findQ_not_In_deqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_rqEdgeUpFrom_sys_minds; eauto.
    - destruct H as [rqUp [down [pidx ?]]]; dest.
      rewrite H1.
      unfold rssQ.
      rewrite findQ_not_In_deqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
  Qed.

  Lemma upLockFreeInv_msgs_preserved:
    forall orqs msgs1 msgs2 oidx,
      UpLockFreeInv orqs msgs1 oidx ->
      (match rqEdgeUpFrom dtr oidx with
       | Some rqUp => findQ rqUp msgs1 = findQ rqUp msgs2
       | None => True
       end) ->
      (match edgeDownTo dtr oidx with
       | Some down => rssQ msgs1 down = rssQ msgs2 down
       | None => True
       end) ->
      UpLockFreeInv orqs msgs2 oidx.
  Proof.
    unfold UpLockFreeInv; simpl; intros.
    destruct H; [left; assumption|right].
    destruct H as [rqUp [down [pidx ?]]]; dest.
    rewrite H in H0.
    rewrite H2 in H1.
    exists rqUp, down, pidx; repeat split;
      try assumption; try congruence.
  Qed.

  Corollary upLockFreeInv_disj_enqMsgs_preserved:
    forall orqs msgs emsgs oidx,
      UpLockFreeInv orqs msgs oidx ->
      DisjList (idsOf emsgs) (sys_minds sys) ->
      UpLockFreeInv orqs (enqMsgs emsgs msgs) oidx.
  Proof.
    intros.
    eapply upLockFreeInv_msgs_preserved; eauto.
    - red in H; dest.
      remember (rqEdgeUpFrom dtr oidx) as rqUp.
      destruct rqUp as [rqUp|]; simpl in *; dest; auto.
      rewrite findQ_not_In_enqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_rqEdgeUpFrom_sys_minds; eauto.
    - red in H; dest.
      remember (edgeDownTo dtr oidx) as down.
      destruct down as [down|]; simpl in *; dest; auto.
      unfold rssQ.
      rewrite findQ_not_In_enqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
  Qed.

  Corollary upLockFreeInv_disj_deqMsgs_preserved:
    forall orqs msgs eminds oidx,
      UpLockFreeInv orqs msgs oidx ->
      DisjList eminds (sys_minds sys) ->
      UpLockFreeInv orqs (deqMsgs eminds msgs) oidx.
  Proof.
    intros.
    eapply upLockFreeInv_msgs_preserved; eauto.
    - red in H; dest.
      remember (rqEdgeUpFrom dtr oidx) as rqUp.
      destruct rqUp as [rqUp|]; simpl in *; dest; auto.
      rewrite findQ_not_In_deqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_rqEdgeUpFrom_sys_minds; eauto.
    - red in H; dest.
      remember (edgeDownTo dtr oidx) as down.
      destruct down as [down|]; simpl in *; dest; auto.
      unfold rssQ.
      rewrite findQ_not_In_deqMsgs.
      + reflexivity.
      + eapply DisjList_In_1; [eassumption|].
        eapply rqrsDTree_edgeDownTo_sys_minds; eauto.
  Qed.

  Lemma upLockedInv_orqs_preserved_parent_eq:
    forall (orqs1 orqs2: ORqs Msg) msgs oidx pidx,
      UpLockedInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs1@[pidx] = orqs2@[pidx] ->
      UpLockedInv orqs2 msgs oidx.
  Proof.
    unfold UpLockedInv; intros.
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    rewrite H3 in H0; inv H0.
    exists rqUp, down, pidx; repeat split; try assumption.
    - red in H6; red; rewrite <-H1; assumption.
    - unfold OLockedTo in *; rewrite <-H1; assumption.
  Qed.

  Corollary upLockedInv_orqs_preserved_self_update:
    forall orqs msgs oidx orq,
      UpLockedInv orqs msgs oidx ->
      UpLockedInv (orqs+[oidx <- orq]) msgs oidx.
  Proof.
    intros.
    destruct Hsd.
    pose proof H.
    destruct H2 as [rqUp [down [pidx ?]]]; dest.
    eapply upLockedInv_orqs_preserved_parent_eq; eauto.
    apply parentIdxOf_not_eq in H4; [|assumption].
    mred.
  Qed.

  Lemma upLockedInv_orqs_preserved_parent_some_up:
    forall (orqs1 orqs2: ORqs Msg) msgs oidx pidx rqiu,
      UpLockedInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[upRq]) = None ->
      orqs2@[pidx] >>= (fun orq2 => orq2@[upRq]) = Some rqiu ->
      edgeDownTo dtr oidx <> Some (rqiu.(rqi_midx_rsb)) ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[downRq]) =
      orqs2@[pidx] >>= (fun orq2 => orq2@[downRq]) ->
      UpLockedInv orqs2 msgs oidx.
  Proof.
    unfold UpLockedInv; intros.
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    rewrite H6 in H0; inv H0.
    exists rqUp, down, pidx; repeat split; try assumption.

    - red in H9; red.
      destruct (orqs1@[pidx]) as [orq1|];
        destruct (orqs2@[pidx]) as [orq2|]; simpl in *;
          try (exfalso; auto; fail); try discriminate.
      + rewrite H2.
        destruct (orq2@[downRq]) as [rqid2|]; auto.
        rewrite H5 in H3.
        left; intro Hx; subst; auto.
      + rewrite H2, <-H4; auto.
    
    - destruct H10.
      + xfst; try assumption.
        intro Hx; red in Hx.
        destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto.
        destruct Hx as [rqi ?]; dest.
        destruct H12.
        * rewrite H2 in H12; inv H12.
          elim H3; assumption.
        * elim H11; red.
          destruct (orqs1@[pidx]) as [orq1|]; simpl in *; auto.
          { eexists; split.
            { right; rewrite H4; eassumption. }
            { assumption. }
          }
          { congruence. }
      + xsnd; try assumption.
        intro Hx; red in Hx.
        destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto.
        destruct Hx as [rqi ?]; dest.
        destruct H12.
        * rewrite H2 in H12; inv H12.
          elim H3; assumption.
        * elim H11; red.
          destruct (orqs1@[pidx]) as [orq1|]; simpl in *; auto.
          { eexists; split.
            { right; rewrite H4; eassumption. }
            { assumption. }
          }
          { congruence. }
      + xthd; try assumption.
        red; red in H11.
        destruct (orqs2@[pidx]) as [orq2|]; simpl in *.
        * destruct (orqs1@[pidx]) as [orq1|]; simpl in *.
          { destruct H11 as [rqi ?]; dest.
            destruct H11.
            { congruence. }
            { eexists; split.
              { right; rewrite <-H4; eassumption. }
              { assumption. }
            }
          }
          { elim H11. }
        * discriminate.
  Qed.

  Lemma upLockedInv_orqs_preserved_parent_some_down:
    forall (orqs1 orqs2: ORqs Msg) msgs oidx pidx rqiu,
      UpLockedInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[downRq]) = None ->
      orqs2@[pidx] >>= (fun orq2 => orq2@[downRq]) = Some rqiu ->
      edgeDownTo dtr oidx <> Some (rqiu.(rqi_midx_rsb)) ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[upRq]) =
      orqs2@[pidx] >>= (fun orq2 => orq2@[upRq]) ->
      UpLockedInv orqs2 msgs oidx.
  Proof.
    unfold UpLockedInv; intros.
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    rewrite H6 in H0; inv H0.
    exists rqUp, down, pidx; repeat split; try assumption.
    - red in H9; red.
      destruct (orqs1@[pidx]) as [orq1|];
        destruct (orqs2@[pidx]) as [orq2|]; simpl in *;
          try (exfalso; auto; fail); try discriminate.
      + rewrite <-H4.
        destruct (orq1@[upRq]) as [rqiu1|]; auto.
        rewrite H2.
        right; intro Hx; subst; auto.
      + rewrite H2, <-H4; auto.

    - destruct H10.
      + xfst; try assumption.
        intro Hx; red in Hx.
        destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto.
        destruct Hx as [rqi ?]; dest.
        destruct H12.
        * elim H11; red.
          destruct (orqs1@[pidx]) as [orq1|]; simpl in *; auto.
          { eexists; split.
            { left; rewrite H4; eassumption. }
            { assumption. }
          }
          { congruence. }
        * rewrite H2 in H12; inv H12.
          elim H3; assumption.
      + xsnd; try assumption.
        intro Hx; red in Hx.
        destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto.
        destruct Hx as [rqi ?]; dest.
        destruct H12.
        * elim H11; red.
          destruct (orqs1@[pidx]) as [orq1|]; simpl in *; auto.
          { eexists; split.
            { left; rewrite H4; eassumption. }
            { assumption. }
          }
          { congruence. }
        * rewrite H2 in H12; inv H12.
          elim H3; assumption.
      + xthd; try assumption.
        red; red in H11.
        destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto.
        * destruct (orqs1@[pidx]) as [orq1|]; simpl in *.
          { destruct H11 as [rqi ?]; dest.
            destruct H11.
            { eexists; split.
              { left; rewrite <-H4; eassumption. }
              { assumption. }
            }
            { congruence. }
          }
          { elim H11. }
        * discriminate.
  Qed.

  Lemma upLockedInv_orqs_preserved_parent_none_up:
    forall (orqs1 orqs2: ORqs Msg) msgs oidx pidx rqiu,
      UpLockedInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[upRq]) = Some rqiu ->
      orqs2@[pidx] >>= (fun orq2 => orq2@[upRq]) = None ->
      edgeDownTo dtr oidx <> Some (rqiu.(rqi_midx_rsb)) ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[downRq]) =
      orqs2@[pidx] >>= (fun orq2 => orq2@[downRq]) ->
      UpLockedInv orqs2 msgs oidx.
  Proof.
    unfold UpLockedInv; intros.
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    rewrite H6 in H0; inv H0.
    exists rqUp, down, pidx; repeat split; try assumption.
    - red in H9; red.
      destruct (orqs1@[pidx]) as [orq1|];
        destruct (orqs2@[pidx]) as [orq2|]; simpl in *;
          auto; try discriminate.
      rewrite H2; auto.
    - destruct H10.
      + xfst; try assumption.
        intro Hx; elim H11; clear H11.
        red in Hx; red.
        destruct (orqs1@[pidx]) as [orq1|];
          destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto;
            try discriminate.
        * destruct Hx as [rqi ?]; dest.
          destruct H11; [congruence|].
          exists rqi; split; auto.
          right; congruence.
        * exfalso; auto.
      + xsnd; try assumption.
        intro Hx; elim H11; clear H11.
        red in Hx; red.
        destruct (orqs1@[pidx]) as [orq1|];
          destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto;
            try discriminate.
        * destruct Hx as [rqi ?]; dest.
          destruct H11; [congruence|].
          exists rqi; split; auto.
          right; congruence.
        * exfalso; auto.
      + xthd; try assumption.
        red; red in H11.
        destruct (orqs1@[pidx]) as [orq1|];
          destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto;
            try discriminate.
        * destruct H11 as [rqi ?]; dest.
          destruct H11; [congruence|].
          eexists; split.
          { right; rewrite <-H4; eassumption. }
          { assumption. }
        * destruct H11 as [rqi ?]; dest.
          destruct H11; [|congruence].
          subst; rewrite H11 in H1; inv H1.
          auto.
  Qed.

  Lemma upLockedInv_orqs_preserved_parent_none_down:
    forall (orqs1 orqs2: ORqs Msg) msgs oidx pidx rqiu,
      UpLockedInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[downRq]) = Some rqiu ->
      orqs2@[pidx] >>= (fun orq2 => orq2@[downRq]) = None ->
      edgeDownTo dtr oidx <> Some (rqiu.(rqi_midx_rsb)) ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[upRq]) =
      orqs2@[pidx] >>= (fun orq2 => orq2@[upRq]) ->
      UpLockedInv orqs2 msgs oidx.
  Proof.
    unfold UpLockedInv; intros.
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    rewrite H6 in H0; inv H0.
    exists rqUp, down, pidx; repeat split; try assumption.
    - red in H9; red.
      destruct (orqs1@[pidx]) as [orq1|];
        destruct (orqs2@[pidx]) as [orq2|]; simpl in *;
          auto; try discriminate.
      rewrite H2.
      destruct (orq2@[upRq]); auto.
    - destruct H10.
      + xfst; try assumption.
        intro Hx; elim H11; clear H11.
        red in Hx; red.
        destruct (orqs1@[pidx]) as [orq1|];
          destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto;
            try discriminate.
        * destruct Hx as [rqi ?]; dest.
          destruct H11; [|congruence].
          exists rqi; split; auto.
          left; congruence.
        * exfalso; auto.
      + xsnd; try assumption.
        intro Hx; elim H11; clear H11.
        red in Hx; red.
        destruct (orqs1@[pidx]) as [orq1|];
          destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto;
            try discriminate.
        * destruct Hx as [rqi ?]; dest.
          destruct H11; [|congruence].
          exists rqi; split; auto.
          left; congruence.
        * exfalso; auto.
      + xthd; try assumption.
        red; red in H11.
        destruct (orqs1@[pidx]) as [orq1|];
          destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto;
            try discriminate.
        * destruct H11 as [rqi ?]; dest.
          destruct H11; [|congruence].
          eexists; split.
          { left; rewrite <-H4; eassumption. }
          { assumption. }
        * destruct H11 as [rqi ?]; dest.
          destruct H11; [congruence|].
          subst; rewrite H11 in H1; inv H1.
          auto.
  Qed.

  Lemma upLockedInv_orqs_preserved_rs_rq:
    forall (orqs1 orqs2: ORqs Msg) msgs oidx pidx rqiu rqid,
      UpLockedInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[upRq]) = Some rqiu ->
      orqs2@[pidx] >>= (fun orq2 => orq2@[upRq]) = None ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[downRq]) = None ->
      orqs2@[pidx] >>= (fun orq2 => orq2@[downRq]) = Some rqid ->
      rqiu.(rqi_midx_rsb) = rqid.(rqi_midx_rsb) ->
      UpLockedInv orqs2 msgs oidx.
  Proof.
    unfold UpLockedInv; intros.
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    rewrite H7 in H0; inv H0.
    exists rqUp, down, pidx; repeat split; try assumption.
    - red in H10; red.
      destruct (orqs1@[pidx]) as [orq1|];
        destruct (orqs2@[pidx]) as [orq2|]; simpl in *;
          auto; try discriminate.
      rewrite H2; auto.
    - destruct H11.
      + xfst; try assumption.
        intro Hx; elim H12; clear H12.
        red in Hx; red.
        destruct (orqs1@[pidx]) as [orq1|];
          destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto;
            try discriminate.
        destruct Hx as [rqi ?]; dest.
        destruct H12; [congruence|].
        exists rqiu; split; auto.
        congruence.
      + xsnd; try assumption.
        intro Hx; elim H12; clear H12.
        red in Hx; red.
        destruct (orqs1@[pidx]) as [orq1|];
          destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto;
            try discriminate.
        destruct Hx as [rqi ?]; dest.
        destruct H12; [congruence|].
        exists rqiu; split; auto.
        congruence.
      + xthd; try assumption.
        red; red in H12.
        destruct (orqs1@[pidx]) as [orq1|];
          destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto;
            try discriminate.
        destruct H12 as [rqi ?]; dest.
        destruct H12; [|congruence].
        eexists; split.
        { right; eassumption. }
        { congruence. }
  Qed.
  
  Corollary upLockedInv_orqs_preserved_non_parent_update:
    forall orqs msgs oidx1 oidx2 orq,
      UpLockedInv orqs msgs oidx1 ->
      parentIdxOf dtr oidx1 <> Some oidx2 ->
      UpLockedInv (orqs+[oidx2 <- orq]) msgs oidx1.
  Proof.
    intros.
    destruct Hsd.
    pose proof H.
    destruct H3 as [rqUp [down [pidx ?]]]; dest.
    eapply upLockedInv_orqs_preserved_parent_eq; eauto.
    mred.
  Qed.

  Lemma upLockFreeInv_orqs_preserved_parent_eq:
    forall (orqs1 orqs2: ORqs Msg) msgs oidx pidx,
      UpLockFreeInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs1@[pidx] = orqs2@[pidx] ->
      UpLockFreeInv orqs2 msgs oidx.
  Proof.
    unfold UpLockFreeInv; intros; dest.
    destruct H; [left; assumption|right].
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    rewrite H3 in H0; inv H0.
    exists rqUp, down, pidx.
    repeat split; try assumption.
    unfold ONoLockTo in *.
    rewrite <-H1; assumption.
  Qed.

  Lemma upLockFreeInv_orqs_preserved_self_update:
    forall orqs msgs oidx orq,
      UpLockFreeInv orqs msgs oidx ->
      UpLockFreeInv (orqs+[oidx <- orq]) msgs oidx.
  Proof.
    unfold UpLockFreeInv; intros; dest.
    destruct H; [left; assumption|right].
    destruct H as [rqUp [down [pidx ?]]]; dest.
    exists rqUp, down, pidx.
    repeat split; try assumption.
    red in H4; red.
    apply parentIdxOf_not_eq in H1; [|destruct Hsd; assumption].
    mred.
  Qed.

  Lemma upLockFreeInv_orqs_preserved_parent_some_up:
    forall (orqs1 orqs2: ORqs Msg) msgs oidx pidx rqiu,
      UpLockFreeInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[upRq]) = None ->
      orqs2@[pidx] >>= (fun orq2 => orq2@[upRq]) = Some rqiu ->
      edgeDownTo dtr oidx <> Some (rqiu.(rqi_midx_rsb)) ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[downRq]) =
      orqs2@[pidx] >>= (fun orq2 => orq2@[downRq]) ->
      UpLockFreeInv orqs2 msgs oidx.
  Proof.
    unfold UpLockFreeInv; intros; dest.
    destruct H; [left; assumption|right].
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    exists rqUp, down, pidx.
    repeat split; try assumption.
    red.
    destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto.
    split.
    - rewrite H2.
      intro Hx; subst; congruence.
    - rewrite H6 in H0; inv H0.
      red in H9.
      destruct (orqs1@[pidx]) as [orq1|]; simpl in *; dest.
      + rewrite <-H4; assumption.
      + rewrite <-H4; auto.
  Qed.

  Lemma upLockFreeInv_orqs_preserved_parent_some_down:
    forall (orqs1 orqs2: ORqs Msg) msgs oidx pidx rqiu,
      UpLockFreeInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[downRq]) = None ->
      orqs2@[pidx] >>= (fun orq2 => orq2@[downRq]) = Some rqiu ->
      edgeDownTo dtr oidx <> Some (rqiu.(rqi_midx_rsb)) ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[upRq]) =
      orqs2@[pidx] >>= (fun orq2 => orq2@[upRq]) ->
      UpLockFreeInv orqs2 msgs oidx.
  Proof.
    unfold UpLockFreeInv; intros; dest.
    destruct H; [left; assumption|right].
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    exists rqUp, down, pidx.
    repeat split; try assumption.
    red.
    destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto.
    split.
    - rewrite H6 in H0; inv H0.
      red in H9.
      destruct (orqs1@[pidx]) as [orq1|]; simpl in *; dest.
      + rewrite <-H4; assumption.
      + rewrite <-H4; auto.
    - rewrite H2.
      intro Hx; subst; congruence.
  Qed.

  Lemma upLockFreeInv_orqs_preserved_parent_none_up:
    forall (orqs1 orqs2: ORqs Msg) msgs oidx pidx,
      UpLockFreeInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs2@[pidx] >>= (fun orq2 => orq2@[upRq]) = None ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[downRq]) =
      orqs2@[pidx] >>= (fun orq2 => orq2@[downRq]) ->
      UpLockFreeInv orqs2 msgs oidx.
  Proof.
    unfold UpLockFreeInv; intros; dest.
    destruct H; [left; assumption|right].
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    rewrite H4 in H0; inv H0.
    exists rqUp, down, pidx.
    repeat split; try assumption.
    red; red in H7; dest.
    destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto.
    split.
    - rewrite H1; auto.
    - destruct (orqs1@[pidx]) as [orq1|]; simpl in *; dest.
      + rewrite <-H2; assumption.
      + rewrite <-H2; auto.
  Qed.

  Lemma upLockFreeInv_orqs_preserved_parent_none_down:
    forall (orqs1 orqs2: ORqs Msg) msgs oidx pidx,
      UpLockFreeInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs2@[pidx] >>= (fun orq2 => orq2@[downRq]) = None ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[upRq]) =
      orqs2@[pidx] >>= (fun orq2 => orq2@[upRq]) ->
      UpLockFreeInv orqs2 msgs oidx.
  Proof.
    unfold UpLockFreeInv; intros; dest.
    destruct H; [left; assumption|right].
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    rewrite H4 in H0; inv H0.
    exists rqUp, down, pidx.
    repeat split; try assumption.
    red; red in H7.
    destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto.
    split.
    - destruct (orqs1@[pidx]) as [orq1|]; simpl in *; dest.
      + rewrite <-H2; assumption.
      + rewrite <-H2; auto.
    - rewrite H1; auto.
  Qed.

  Lemma upLockFreeInv_orqs_preserved_rs_rq:
    forall (orqs1 orqs2: ORqs Msg) msgs oidx pidx rqiu rqid,
      UpLockFreeInv orqs1 msgs oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[upRq]) = Some rqiu ->
      orqs2@[pidx] >>= (fun orq2 => orq2@[upRq]) = None ->
      orqs1@[pidx] >>= (fun orq1 => orq1@[downRq]) = None ->
      orqs2@[pidx] >>= (fun orq2 => orq2@[downRq]) = Some rqid ->
      rqiu.(rqi_midx_rsb) = rqid.(rqi_midx_rsb) ->
      UpLockFreeInv orqs2 msgs oidx.
  Proof.
    unfold UpLockFreeInv; intros; dest.
    destruct H; [left; assumption|right].
    destruct H as [rqUp [down [pidx' ?]]]; dest.
    rewrite H7 in H0; inv H0.
    exists rqUp, down, pidx.
    repeat split; try assumption.
    red; red in H10.
    destruct (orqs2@[pidx]) as [orq2|]; simpl in *; auto.
    split.
    - rewrite H2; auto.
    - rewrite H4.
      destruct (orqs1@[pidx]) as [orq1|]; simpl in *; dest.
      + rewrite H1 in H0; congruence.
      + discriminate.
  Qed.

  Corollary upLockFreeInv_orqs_preserved_non_parent_update:
    forall orqs msgs oidx1 oidx2 orq,
      UpLockFreeInv orqs msgs oidx1 ->
      parentIdxOf dtr oidx1 <> Some oidx2 ->
      UpLockFreeInv (orqs+[oidx2 <- orq]) msgs oidx1.
  Proof.
    intros.
    destruct Hsd.
    pose proof H.
    destruct H3; [left; assumption|].
    destruct H3 as [rqUp [down [pidx ?]]]; dest.
    eapply upLockFreeInv_orqs_preserved_parent_eq; eauto.
    mred.
  Qed.

  Lemma upLockInv_step_ext_in:
    forall oss orqs msgs eins,
      UpLockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eins <> nil ->
      ValidMsgsExtIn sys eins ->
      UpLockInv {| bst_oss := oss;
                   bst_orqs := orqs;
                   bst_msgs := enqMsgs eins msgs |}.
  Proof.
    unfold UpLockInv; simpl; intros.
    red; intros.
    specialize (H oidx H2).

    destruct H1.
    assert (DisjList (idsOf eins) (sys_minds sys)).
    { eapply DisjList_SubList; eauto.
      apply DisjList_comm.
      apply sys_minds_sys_merqs_DisjList.
    }
    
    destruct (orqs@[oidx]) as [orq|]; simpl in *; dest.
    - red in H; red.
      remember (orq@[upRq]) as orqi.
      destruct orqi as [rqi|].
      + apply upLockedInv_disj_enqMsgs_preserved; assumption.
      + apply upLockFreeInv_disj_enqMsgs_preserved; assumption.
    - red in H; simpl in H.
      red in H3; simpl in H3.
      red; simpl.
      apply upLockFreeInv_disj_enqMsgs_preserved; assumption.
  Qed.

  Lemma upLockInv_step_ext_out:
    forall oss orqs msgs eouts,
      UpLockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eouts <> nil ->
      Forall (FirstMPI msgs) eouts ->
      ValidMsgsExtOut sys eouts ->
      UpLockInv {| bst_oss := oss;
                   bst_orqs := orqs;
                   bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    unfold UpLockInv; simpl; intros.
    red; intros.
    specialize (H oidx H3).

    destruct H2.
    assert (DisjList (idsOf eouts) (sys_minds sys)).
    { eapply DisjList_SubList; eauto.
      apply DisjList_comm.
      apply sys_minds_sys_merss_DisjList.
    }
    
    destruct (orqs@[oidx]) as [orq|]; simpl in *; dest.
    - red in H; red.
      remember (orq@[upRq]) as orqi.
      destruct orqi as [rqi|].
      + apply upLockedInv_disj_deqMsgs_preserved; assumption.
      + apply upLockFreeInv_disj_deqMsgs_preserved; assumption.
    - red in H; simpl in H.
      red in H4; simpl in H4.
      red; simpl.
      apply upLockFreeInv_disj_deqMsgs_preserved; assumption.
  Qed.

  Section InternalStep.
    Variables (oss: OStates oifc) (orqs: ORqs Msg) (msgs: MessagePool Msg)
              (obj: Object oifc) (rule: Rule oifc)
              (post: OState oifc) (porq: ORq Msg) (mins: list (Id Msg))
              (nost: OState oifc) (norq: ORq Msg) (mouts: list (Id Msg)).

    Hypotheses
      (Hfpok: FootprintsOk
                dtr sys {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |})
      (HobjIn: In obj (sys_objs sys))
      (HruleIn: In rule (obj_rules obj))
      (Hporq: orqs@[obj_idx obj] = Some porq)
      (Hpost: oss@[obj_idx obj] = Some post)
      (HminsF: Forall (FirstMPI msgs) mins)
      (HminsV: ValidMsgsIn sys mins)
      (Hprec: rule_precond rule post porq mins)
      (Htrs: rule_trs rule post porq mins = (nost, norq, mouts))
      (HmoutsV: ValidMsgsOut sys mouts)
      (Hmdisj: DisjList (idsOf mins) (idsOf mouts)).

    Lemma deqMP_rq_filter_rs_eq:
      forall midx msg,
        msg_type msg = MRq ->
        FirstMPI msgs (midx, msg) ->
        filter (fun msg => msg_type msg ==n MRs)
               (findQ midx msgs) =
        filter (fun msg => msg_type msg ==n MRs)
               (findQ midx (deqMP midx msgs)).
    Proof.
      intros.
      unfold FirstMPI, FirstMP, firstMP in H0.
      unfold deqMP, idOf in *; simpl in *.
      destruct (findQ midx msgs); [discriminate|].
      simpl in H0; inv H0.
      unfold findQ; mred; simpl.
      rewrite H; simpl.
      reflexivity.
    Qed.

    Lemma deqMP_rs_filter_rq_eq:
      forall midx msg,
        msg_type msg = MRs ->
        FirstMPI msgs (midx, msg) ->
        filter (fun msg => msg_type msg ==n MRq)
               (findQ midx msgs) =
        filter (fun msg => msg_type msg ==n MRq)
               (findQ midx (deqMP midx msgs)).
    Proof.
      intros.
      unfold FirstMPI, FirstMP, firstMP in H0.
      unfold deqMP, idOf in *; simpl in *.
      destruct (findQ midx msgs); [discriminate|].
      simpl in H0; inv H0.
      unfold findQ; mred; simpl.
      rewrite H; simpl.
      reflexivity.
    Qed.

    Ltac disc_rule_custom ::=
      match goal with
      | [H: FootprintUpOkEx _ _ _ /\ _ |- _] => destruct H
      | [H: _ /\ FootprintDownOkEx _ _ _ _ |- _] => destruct H
      | [H: FootprintUpOkEx _ _ _ |- _] =>
        let rqFrom := fresh "rqFrom" in
        let rqTo := fresh "rqTo" in
        let rsFrom := fresh "rsFrom" in
        let rsbTo := fresh "rsbTo" in
        destruct H as [rqFrom [rqTo [rsFrom [rsbTo ?]]]]; dest
      | [H: FootprintUpOk _ _ _ _ _ _ |- _] =>
        let cidx := fresh "cidx" in
        destruct H as [cidx ?]; dest

      | [H: FootprintDownOkEx _ _ _ _ |- _] =>
        let rqFrom := fresh "rqFrom" in
        let rqTos := fresh "rqTos" in
        let rssFrom := fresh "rssFrom" in
        let rsbTo := fresh "rsbTo" in
        destruct H as [rqFrom [rqTos [rssFrom [rsbTo ?]]]]; dest
      | [H: FootprintUpDownOk _ _ _ _ _ _ _ \/
            FootprintDownDownOk _ _ _ _ _ _ |- _] => destruct H
      | [H: exists _, FootprintUpDownOk _ _ _ _ _ _ _ |- _] =>
        let rqFrom := fresh "rqFrom" in
        destruct H as [rqFrom ?]
      | [H: FootprintUpDownOk _ _ _ _ _ _ _ |- _] =>
        let upCIdx := fresh "upCIdx" in
        let upCObj := fresh "upCObj" in
        destruct H as [upCIdx [upCObj ?]]; dest
      | [H: FootprintDownDownOk _ _ _ _ _ _ |- _] => red in H; dest
      end.

    Lemma upLockInvORq_step_int_me:
      UpLockInvORq orqs msgs (obj_idx obj) porq ->
      In (obj_idx obj) (map (@obj_idx _) (sys_objs sys)) ->
      GoodRqRsRule dtr sys (obj_idx obj) rule ->
      UpLockInvORq (orqs+[obj_idx obj <- norq])
                   (enqMsgs mouts (deqMsgs (idsOf mins) msgs))
                   (obj_idx obj) norq.
    Proof.
      intros.
      destruct Hsd.
      red in H; red.
      good_rqrs_rule_cases rule.

      - (** case [ImmDownRule] *)
        disc_rule_conds.
        apply upLockFreeInv_orqs_preserved_self_update.
        eapply upLockFreeInv_msgs_preserved; eauto.
        + remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
          destruct orqUp as [rqUp|]; auto.
          solve_q.
        + remember (edgeDownTo dtr (obj_idx obj)) as odown.
          destruct odown as [down|]; auto.
          solve_q.

      - (** case [ImmUpRule] *)
        disc_rule_conds.
        destruct (norq@[upRq]).
        + apply upLockedInv_orqs_preserved_self_update.
          eapply upLockedInv_msgs_preserved; eauto.
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
          * disc_rule_conds.
            solve_q.
            eapply deqMP_rq_filter_rs_eq; eauto.
        + apply upLockFreeInv_orqs_preserved_self_update.
          eapply upLockFreeInv_msgs_preserved; eauto.
          * remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
            destruct orqUp as [rqUp|]; auto.
            solve_q.
          * disc_rule_conds.
            solve_q.
            eapply deqMP_rq_filter_rs_eq; eauto.

      - (** case [RqFwdRule] *)
        disc_rule_conds.
        + (** case [RqUpUp]; setting an uplock. *)
          apply upLockedInv_orqs_preserved_self_update.
          red in H.
          pose proof (rqEdgeUpFrom_Some Hsd _ H5).
          destruct H10 as [rsUp [down [pidx ?]]]; dest.
          disc_rule_conds.
          destruct H; [discriminate|].
          destruct H as [rqUp [down' [pidx' ?]]]; dest.
          disc_rule_conds.
          do 3 eexists; repeat split; try eassumption.
          * solve_q.
            rewrite H19; simpl; omega.
          * solve_q.
            unfold rssQ in H20; rewrite H20.
            simpl; omega.
          * apply ONoLockTo_ONoSameLockTo; assumption.
          * xfst.
            { solve_q.
              rewrite H19; reflexivity.
            }
            { solve_q.
              unfold rssQ in H20; rewrite H20; auto.
            }
            { apply ONoLockTo_not_OLockedTo; assumption. }

        + (** case [RqUpDown]; setting a downlock. *)
          remember (porq@[upRq]) as orqiu; destruct orqiu as [rqiu|].
          * apply upLockedInv_orqs_preserved_self_update.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              rewrite H.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }

          * apply upLockFreeInv_orqs_preserved_self_update.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr (obj_idx obj)) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }

        + (** case [RqDownDown]; setting a downlock *)
          remember (porq@[upRq]) as orqiu; destruct orqiu as [rqiu|].
          * apply upLockedInv_orqs_preserved_self_update.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { red in H; destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
            { red in H; destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
              eapply deqMP_rq_filter_rs_eq; eauto.
            }

          * apply upLockFreeInv_orqs_preserved_self_update.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr (obj_idx obj)) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
                eapply deqMP_rq_filter_rs_eq; eauto.
              }
            }

      - (** case [RsBackRule] *)
        good_footprint_get (obj_idx obj).
        disc_rule_conds.
        + (** case [FootprintReleasingUp]; releasing the uplock. *)
          apply upLockFreeInv_orqs_preserved_self_update.
          destruct i as [rsDown rsbm]; simpl in *.
          destruct H as [rqUp [down [pidx ?]]]; dest.
          disc_rule_conds.
          xor3_inv2 H20; [dest|eapply rssQ_length_one; eauto].
          remember (rqi_midx_rsb rqi) as rsbTo; clear HeqrsbTo.
          right.
          exists rqTo, rsDown, pidx.
          repeat split; try assumption.
          * solve_q.
            apply length_zero_iff_nil; omega.
          * solve_q.
            apply findQ_In_deqMP_FirstMP in H9; simpl in H9.
            unfold rssQ in H18; rewrite <-H9 in H18.
            simpl in H18; rewrite H12 in H18; simpl in H18.
            apply length_zero_iff_nil; omega.
          * apply not_ONoLockTo_OLockedTo; auto.
          
        + (** case [FootprintReleasingDown]-1 *)
          remember (porq@[upRq]) as orqiu; destruct orqiu as [rqiu|].
          * apply upLockedInv_orqs_preserved_self_update.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              rewrite H17.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              rewrite H17.
              solve_q.
            }              
          * apply upLockFreeInv_orqs_preserved_self_update.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                rewrite H17.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr (obj_idx obj)) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                rewrite H17.
                solve_q.
              }
            }

        + (** case [FootprintReleasingDown]-2 *)
          remember (porq@[upRq]) as orqiu; destruct orqiu as [rqiu|].
          * apply upLockedInv_orqs_preserved_self_update.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              rewrite H17.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              rewrite H17.
              solve_q.
            }
          * apply upLockFreeInv_orqs_preserved_self_update.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr (obj_idx obj)) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                rewrite H17.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr (obj_idx obj)) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                rewrite H17.
                solve_q.
              } 
            }

      - (** case [RsDownRqDownRule] *)
        disc_rule_conds.
        apply upLockFreeInv_orqs_preserved_self_update.
        destruct H as [rqUp [down [pidx ?]]]; dest.
        disc_rule_conds.
        xor3_inv2 H17; [dest|eapply rssQ_length_one; eauto].
        red; right.
        exists rqUp, rsFrom, pidx; repeat split; try assumption.
        + solve_q.
          apply length_zero_iff_nil; omega.
        + solve_q.
          apply findQ_In_deqMP_FirstMP in H7; simpl in H7.
          unfold rssQ in H14; rewrite <-H7 in H14.
          simpl in H14; rewrite H5 in H14; simpl in H14.
          apply length_zero_iff_nil; omega.
        + apply not_ONoLockTo_OLockedTo; auto.
    Qed.

    Lemma upLockInvORq_step_int_parent:
      forall oidx,
        UpLockInvORq orqs msgs oidx ((orqs@[oidx]) >>=[[]] (fun orq => orq)) ->
        In oidx (map (@obj_idx _) (sys_objs sys)) ->
        GoodRqRsRule dtr sys (obj_idx obj) rule ->
        parentIdxOf dtr oidx = Some (obj_idx obj) ->
        UpLockInvORq (orqs+[obj_idx obj <- norq])
                     (enqMsgs mouts (deqMsgs (idsOf mins) msgs)) oidx
                     ((orqs@[ oidx]) >>=[[]] (fun orq => orq)).
    Proof.
      intros.
      destruct Hsd.
      red in H; red.
      good_rqrs_rule_cases rule.

      - (** case [ImmDownRule] *)
        find_if_inside.
        + eapply upLockedInv_orqs_preserved_parent_eq with (orqs1:= orqs).
          * disc_rule_conds.
            destruct (eq_nat_dec cidx oidx); subst.
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              exists rqUp, down, pidx.
              disc_rule_conds.

              assert (length (rssQ (enqMP rsTo rsm (deqMP rqFrom msgs)) rsTo) = 1).
              { solve_q.
                rewrite filter_app; simpl.
                rewrite H6; simpl.
                rewrite app_length; simpl.
                xor3_inv1 H14; dest.
                { unfold rssQ in H2, H9; omega. }
                { eapply findQ_length_one; eauto. }
              }
              rewrite H2; clear H2.

              solve_q.
              repeat split; try assumption.
              { apply findQ_In_deqMP_FirstMP in H11; simpl in H11.
                rewrite <-H11 in H7; simpl in H7.
                omega.
              }
              { omega. }
              { xsnd.
                { apply findQ_In_deqMP_FirstMP in H11; simpl in H11.
                  rewrite <-H11 in H7; simpl in H7.
                  omega.
                }
                { reflexivity. }
                { apply ONoLockTo_not_OLockedTo.
                  red; disc_rule_conds; auto.
                }
              }
            }
            { eapply parentIdxOf_Some in H2; [|eassumption].
              destruct H2 as [rqUp [rsUp [down ?]]]; dest.
              eapply upLockedInv_msgs_preserved; [eassumption| |].
              { disc_rule_conds; solve_q. }
              { disc_rule_conds; solve_q. }
            }
          * eassumption.
          * disc_rule_conds.
          
        + eapply upLockFreeInv_orqs_preserved_parent_eq with (orqs1:= orqs).
          * disc_rule_conds.
            destruct (eq_nat_dec cidx oidx); subst.
            { exfalso.
              destruct H; [congruence|].
              destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              apply FirstMP_InMP in H11.
              red in H11; simpl in H11; rewrite H7 in H11.
              elim H11.
            }
            { destruct H; [left; assumption|right].
              destruct H as [rqUp [down [pidx ?]]]; dest.
              exists rqUp, down, pidx.
              repeat split; try assumption.
              { solve_q; assumption. }
              { solve_q; assumption. }
            }
          * eassumption.
          * disc_rule_conds.

      - (** case [ImmUpRule] *)
        find_if_inside.
        + disc_rule_conds.
          eapply upLockedInv_orqs_preserved_parent_eq with (orqs1:= orqs);
            [|eassumption|mred].
          apply upLockedInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
        + disc_rule_conds.
          eapply upLockFreeInv_orqs_preserved_parent_eq with (orqs1:= orqs);
            [|eassumption|mred].
          apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H.
            { remember (rqEdgeUpFrom dtr oidx) as orqUp.
              destruct orqUp; auto.
              eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * destruct H.
            { remember (edgeDownTo dtr oidx) as odown.
              destruct odown; auto.
              eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }

      - (** case [RqFwdRule] *)
        disc_rule_conds.
        + (** case [RqUpUp] *)
          destruct (eq_nat_dec cidx oidx); subst.
          * find_if_inside.
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              exists rqUp, down, pidx.
              disc_rule_conds.

              xor3_inv1 H21; [dest|eapply findQ_length_one; eauto].

              assert (length (findQ rqFrom (enqMP rqTo rqtm (deqMP rqFrom msgs))) = 0).
              { solve_q.
                apply findQ_In_deqMP_FirstMP in H14; simpl in H14.
                rewrite <-H14 in H16; simpl in H16.
                omega.
              }
              rewrite H5; clear H5.

              assert (length (rssQ (enqMP rqTo rqtm (deqMP rqFrom msgs))
                                   (rqi_midx_rsb rqi)) = 0).
              { solve_q.
                unfold rssQ in H1, H19; omega.
              }
              rewrite H5; clear H5.

              repeat split; try assumption; try omega.
              { unfold ONoSameLockTo, OLockedTo in *.
                mred; simpl; mred.
                destruct (porq@[downRq]) as [rqid|]; auto.
                right.
                intro Hx; elim H2; eauto.
              }
              { xthd; try discriminate.
                red; mred; simpl; mred.
                eexists; split; [left; reflexivity|reflexivity].
              }
            }
            { destruct H; [left; assumption|right].
              destruct H as [rqUp [down [pidx ?]]]; dest.
              exfalso.
              disc_rule_conds.
              apply FirstMP_InMP in H14.
              red in H14; simpl in H14; rewrite H16 in H14.
              elim H14.
            }
          * find_if_inside.
            { apply upLockedInv_orqs_preserved_parent_some_up
                with (orqs1:= orqs) (pidx:= obj_idx obj) (rqiu:= rqi);
                auto; try (repeat (mred; simpl); fail).
              { eapply upLockedInv_msgs_preserved; [eassumption| |].
                { destruct H as [rqUp [down [pidx ?]]]; dest.
                  disc_rule_conds.
                  solve_q.
                }
                { destruct H as [rqUp [down [pidx ?]]]; dest.
                  disc_rule_conds.
                  solve_q.
                }
              }
              { intro Hx.
                elim (rqrsDTree_down_down_not_eq Hsd n H9 Hx).
                reflexivity.
              }
            }
            { apply upLockFreeInv_orqs_preserved_parent_some_up
                with (orqs1:= orqs) (pidx:= obj_idx obj) (rqiu:= rqi);
                auto; try (repeat (mred; simpl); fail).
              { eapply upLockFreeInv_msgs_preserved; [eassumption| |].
                { destruct H.
                  { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                    destruct orqUp; auto.
                    eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                    dest; disc_rule_conds.
                  }
                  { destruct H as [rqUp [down [pidx ?]]]; dest.
                    disc_rule_conds.
                    solve_q.
                  }
                }
                { destruct H.
                  { remember (edgeDownTo dtr oidx) as odown.
                    destruct odown; auto.
                    eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                    dest; disc_rule_conds.
                  }
                  { destruct H as [rqUp [down [pidx ?]]]; dest.
                    disc_rule_conds.
                    solve_q.
                  }
                }
              }
              { intro Hx.
                elim (rqrsDTree_down_down_not_eq Hsd n H9 Hx).
                reflexivity.
              }
            }

        + (** case [RqUpDown] *)
          destruct (eq_nat_dec (obj_idx upCObj) oidx); subst.
          * find_if_inside.
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              exists rqUp, down, pidx.
              disc_rule_conds.

              xor3_inv1 H20; [dest|eapply findQ_length_one; eauto].

              assert (length (findQ rqFrom (enqMsgs mouts (deqMP rqFrom msgs))) = 0).
              { solve_q.
                apply findQ_In_deqMP_FirstMP in H14; simpl in H14.
                rewrite <-H14 in H16; simpl in H16.
                omega.
              }
              rewrite H7; clear H7.

              assert (length (rssQ (enqMsgs mouts (deqMP rqFrom msgs))
                                   (rqi_midx_rsb rqi)) = 0).
              { solve_q.
                unfold rssQ in H2, H17; omega.
              }
              rewrite H7; clear H7.

              repeat split; try assumption; try omega.
              { unfold ONoSameLockTo, OLockedTo in *.
                mred; simpl; mred.
                destruct (porq@[upRq]) as [rqiu|]; auto.
                left.
                intro Hx; elim H6; eauto.
              }
              { xthd; try discriminate.
                red; mred; simpl; mred.
                eexists; split; [right; reflexivity|reflexivity].
              }
            }
            { destruct H; [left; assumption|right].
              destruct H as [rqUp [down [pidx ?]]]; dest.
              exfalso.
              disc_rule_conds.
              apply FirstMP_InMP in H14.
              red in H14; simpl in H14; rewrite H16 in H14.
              elim H14.
            }
          * find_if_inside.
            { apply upLockedInv_orqs_preserved_parent_some_down
                with (orqs1:= orqs) (pidx:= obj_idx obj) (rqiu:= rqi);
                auto; try (repeat (mred; simpl); fail).
              { eapply upLockedInv_msgs_preserved; [eassumption| |].
                { destruct H as [rqUp [down [pidx ?]]]; dest.
                  disc_rule_conds.
                  solve_q.
                }
                { destruct H as [rqUp [down [pidx ?]]]; dest.
                  disc_rule_conds.
                  rewrite rssQ_enqMsgs_rqs by assumption.
                  solve_q.
                }
              }
              { intro Hx.
                elim (rqrsDTree_down_down_not_eq Hsd n H9 Hx).
                reflexivity.
              }
            }
            { apply upLockFreeInv_orqs_preserved_parent_some_down
                with (orqs1:= orqs) (pidx:= obj_idx obj) (rqiu:= rqi);
                auto; try (repeat (mred; simpl); fail).
              { eapply upLockFreeInv_msgs_preserved; [eassumption| |].
                { destruct H.
                  { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                    destruct orqUp; auto.
                    eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                    dest; disc_rule_conds.
                  }
                  { destruct H as [rqUp [down [pidx ?]]]; dest.
                    disc_rule_conds.
                    solve_q.
                  }
                }
                { destruct H.
                  { remember (edgeDownTo dtr oidx) as odown.
                    destruct odown; auto.
                    eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                    dest; disc_rule_conds.
                  }
                  { destruct H as [rqUp [down [pidx ?]]]; dest.
                    disc_rule_conds.
                    rewrite rssQ_enqMsgs_rqs by assumption.
                    solve_q.
                  }
                }
              }
              { intro Hx.
                elim (rqrsDTree_down_down_not_eq Hsd n H9 Hx).
                reflexivity.
              }
            }

        + (** case [RqDownDown] *)
          find_if_inside.
          * apply upLockedInv_orqs_preserved_parent_some_down
              with (orqs1:= orqs) (pidx:= obj_idx obj) (rqiu:= rqi);
              auto; try (repeat (mred; simpl); fail).
            { apply upLockedInv_msgs_preserved with (msgs1:= msgs);
                [assumption| |].
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                rewrite rssQ_enqMsgs_rqs by assumption.
                solve_q.
              }
            }
            { intro Hx.
              elim (rqrsDTree_rsUp_down_not_eq Hsd _ _ H5 Hx).
              reflexivity.
            }
          * apply upLockFreeInv_orqs_preserved_parent_some_down
              with (orqs1:= orqs) (pidx:= obj_idx obj) (rqiu:= rqi);
              auto; try (repeat (mred; simpl); fail).
            { apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
                [assumption| |].
              { destruct H.
                { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                  destruct orqUp; auto.
                  eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                  dest; disc_rule_conds.
                }
                { destruct H as [rqUp [down [pidx ?]]]; dest.
                  disc_rule_conds.
                  solve_q.
                }
              }
              { destruct H.
                { remember (edgeDownTo dtr oidx) as odown.
                  destruct odown; auto.
                  eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                  dest; disc_rule_conds.
                }
                { destruct H as [rqUp [down [pidx ?]]]; dest.
                  disc_rule_conds.
                  rewrite rssQ_enqMsgs_rqs by assumption.
                  solve_q.
                }
              }
            }
            { intro Hx.
              elim (rqrsDTree_rsUp_down_not_eq Hsd _ _ H5 Hx).
              reflexivity.
            }

      - (** case [RsBackRule] *)
        good_footprint_get (obj_idx obj).
        disc_rule_conds.
        + (** case [FootprintReleasingUp] *)
          destruct (eq_nat_dec cidx oidx); subst.
          * find_if_inside.
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              exists rqUp, down, pidx.
              disc_rule_conds.

              xor3_inv3 H21; [dest|red; disc_rule_conds; eexists; intuition].

              assert (length (findQ rqFrom (enqMP (rqi_midx_rsb rqi) rsm (deqMP (fst i) msgs))) = 0).
              { solve_q; omega. }
              rewrite H7; clear H7.

              assert (length
                        (rssQ (enqMP (rqi_midx_rsb rqi) rsm (deqMP (fst i) msgs))
                              (rqi_midx_rsb rqi)) = 1).
              { solve_q.
                rewrite filter_app; simpl.
                rewrite H8; simpl.
                rewrite app_length; simpl.
                unfold rssQ in H6, H19; omega.
              }
              rewrite H7; clear H7.

              repeat split; try assumption; try omega.
              { red; mred; simpl; mred. }
              { xsnd; [discriminate|reflexivity|].
                apply ONoLockTo_not_OLockedTo.
                red in H20; red; mred.
                simpl; mred; split; auto.
              }
            }
            { destruct H; [left; assumption|right].
              destruct H as [rqUp [down [pidx ?]]]; dest.
              exfalso.
              disc_rule_conds.
              red in H20; mred.
            }
          * find_if_inside.
            { apply upLockedInv_orqs_preserved_parent_none_up
                with (orqs1:= orqs) (pidx:= obj_idx obj) (rqiu:= rqi);
                auto; try (repeat (mred; simpl); fail).
              { eapply upLockedInv_msgs_preserved; [eassumption| |].
                { destruct H as [rqUp [down [pidx ?]]]; dest.
                  disc_rule_conds.
                  solve_q.
                }
                { destruct H as [rqUp [down [pidx ?]]]; dest.
                  disc_rule_conds.
                  solve_q.
                }
              }
              { intro Hx.
                elim (rqrsDTree_down_down_not_eq Hsd n H15 Hx).
                reflexivity.
              }
            }
            { apply upLockFreeInv_orqs_preserved_parent_none_up
                with (orqs1:= orqs) (pidx:= obj_idx obj);
                auto; try (repeat (mred; simpl); fail).
              eapply upLockFreeInv_msgs_preserved; [eassumption| |].
              { destruct H.
                { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                  destruct orqUp; auto.
                  eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                  dest; disc_rule_conds.
                }
                { destruct H as [rqUp [down [pidx ?]]]; dest.
                  disc_rule_conds.
                  solve_q.
                }
              }
              { destruct H.
                { remember (edgeDownTo dtr oidx) as odown.
                  destruct odown; auto.
                  eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                  dest; disc_rule_conds.
                }
                { destruct H as [rqUp [down [pidx ?]]]; dest.
                  disc_rule_conds.
                  solve_q.
                }
              }
            }

        + (** case [FootprintReleasingDown]-1 *)
          destruct (eq_nat_dec (obj_idx upCObj) oidx); subst.
          * find_if_inside.
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              exists rqUp, down, pidx.
              disc_rule_conds.

              xor3_inv3 H20; [dest|red; disc_rule_conds; eexists; intuition].

              assert (length (findQ rqFrom (enqMP (rqi_midx_rsb rqi) rsm (deqMsgs (idsOf mins) msgs))) = 0).
              { rewrite H18; solve_q.
                omega.
              }
              rewrite H11; clear H11.

              assert (length
                        (rssQ (enqMP (rqi_midx_rsb rqi) rsm (deqMsgs (idsOf mins) msgs))
                              (rqi_midx_rsb rqi)) = 1).
              { rewrite H18; solve_q.
                rewrite filter_app; simpl.
                rewrite H8; simpl.
                rewrite app_length; simpl.
                unfold rssQ in H10, H17; omega.
              }
              rewrite H11; clear H11.

              repeat split; try assumption; try omega.
              { red; mred; simpl; mred.
                destruct (porq@[upRq]); auto.
              }
              { xsnd; [discriminate|reflexivity|].
                apply ONoLockTo_not_OLockedTo.
                red in H19; red; mred.
                simpl; split.
                { mred.
                  destruct (porq@[upRq]) as [rqiu|]; auto.
                  destruct H19; auto.
                }
                { mred. }
              }
            }
            { destruct H; [left; assumption|right].
              destruct H as [rqUp [down [pidx ?]]]; dest.
              exfalso.
              disc_rule_conds.
              red in H19; mred.
            }
          * find_if_inside.
            { apply upLockedInv_orqs_preserved_parent_none_down
                with (orqs1:= orqs) (pidx:= obj_idx obj) (rqiu:= rqi);
                auto; try (repeat (mred; simpl); fail).
              { eapply upLockedInv_msgs_preserved; [eassumption| |].
                { destruct H as [rqUp [down [pidx ?]]]; dest.
                  disc_rule_conds.
                  rewrite H18; solve_q.
                }
                { destruct H as [rqUp [down [pidx ?]]]; dest.
                  disc_rule_conds.
                  rewrite H18; solve_q.
                }
              }
              { intro Hx.
                elim (rqrsDTree_down_down_not_eq Hsd n H11 Hx).
                reflexivity.
              }
            }
            { apply upLockFreeInv_orqs_preserved_parent_none_down
                with (orqs1:= orqs) (pidx:= obj_idx obj);
                auto; try (repeat (mred; simpl); fail).
              eapply upLockFreeInv_msgs_preserved; [eassumption| |].
              { destruct H.
                { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                  destruct orqUp; auto.
                  eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                  dest; disc_rule_conds.
                }
                { destruct H as [rqUp [down [pidx ?]]]; dest.
                  disc_rule_conds.
                  rewrite H18; solve_q.
                }
              }
              { destruct H.
                { remember (edgeDownTo dtr oidx) as odown.
                  destruct odown; auto.
                  eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                  dest; disc_rule_conds.
                }
                { destruct H as [rqUp [down [pidx ?]]]; dest.
                  disc_rule_conds.
                  rewrite H18; solve_q.
                }
              }
            }

        + (** case [FootprintReleasingDown]-2 *)
          find_if_inside.
          * apply upLockedInv_orqs_preserved_parent_none_down
              with (orqs1:= orqs) (pidx:= obj_idx obj) (rqiu:= rqi);
              auto; try (repeat (mred; simpl); fail).
            { eapply upLockedInv_msgs_preserved; [eassumption| |].
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                rewrite H18; solve_q.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                rewrite H18; solve_q.
              }
            }
            { intro Hx.
              elim (rqrsDTree_rsUp_down_not_eq Hsd _ _ H6 Hx).
              reflexivity.
            }
          * apply upLockFreeInv_orqs_preserved_parent_none_down
              with (orqs1:= orqs) (pidx:= obj_idx obj);
              auto; try (repeat (mred; simpl); fail).
            eapply upLockFreeInv_msgs_preserved; [eassumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                rewrite H18; solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr oidx) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                rewrite H18; solve_q.
              }
            }

      - (** case [RsDownRqDownRule] *)
        find_if_inside.
        + disc_rule_conds.
          eapply upLockedInv_orqs_preserved_rs_rq
            with (orqs1:= orqs) (pidx:= obj_idx obj) (rqiu:= rqi1) (rqid:= rqi0);
            auto; try (repeat (mred; simpl); fail).
          eapply upLockedInv_msgs_preserved; [eassumption| |].
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            rewrite rssQ_enqMsgs_rqs by assumption.
            solve_q.
        + disc_rule_conds.
          eapply upLockFreeInv_orqs_preserved_rs_rq
            with (orqs1:= orqs) (pidx:= obj_idx obj) (rqiu:= rqi1) (rqid:= rqi0);
            auto; try (repeat (mred; simpl); fail).
          eapply upLockFreeInv_msgs_preserved; [eassumption| |].
          * destruct H.
            { remember (rqEdgeUpFrom dtr oidx) as orqUp.
              destruct orqUp; auto.
              eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * destruct H.
            { remember (edgeDownTo dtr oidx) as odown.
              destruct odown; auto.
              eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              rewrite rssQ_enqMsgs_rqs by assumption.
              solve_q.
            }
    Qed.

    Lemma upLockInvORq_step_int_other:
      forall oidx orq,
        UpLockInvORq orqs msgs oidx orq ->
        In oidx (map (@obj_idx _) (sys_objs sys)) ->
        GoodRqRsRule dtr sys (obj_idx obj) rule ->
        obj_idx obj <> oidx ->
        parentIdxOf dtr oidx <> Some (obj_idx obj) ->
        UpLockInvORq (orqs+[obj_idx obj <- norq])
                     (enqMsgs mouts (deqMsgs (idsOf mins) msgs)) oidx
                     orq.
    Proof.
      intros.
      destruct Hsd.
      red in H; red.
      good_rqrs_rule_cases rule.

      - (** case [ImmDownRule] *)
        find_if_inside.
        + apply upLockedInv_orqs_preserved_non_parent_update; auto.
          apply upLockedInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
        + apply upLockFreeInv_orqs_preserved_non_parent_update; auto.
          apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H.
            { remember (rqEdgeUpFrom dtr oidx) as orqUp.
              destruct orqUp; auto.
              eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * destruct H.
            { remember (edgeDownTo dtr oidx) as odown.
              destruct odown; auto.
              eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }

      - (** case [ImmUpRule] *)
        find_if_inside.
        + apply upLockedInv_orqs_preserved_non_parent_update; auto.
          apply upLockedInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
        + apply upLockFreeInv_orqs_preserved_non_parent_update; auto.
          apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H.
            { remember (rqEdgeUpFrom dtr oidx) as orqUp.
              destruct orqUp; auto.
              eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * destruct H.
            { remember (edgeDownTo dtr oidx) as odown.
              destruct odown; auto.
              eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
        
      - (** case [RqFwdRule] *)
        disc_rule_conds.

        + find_if_inside.
          * apply upLockedInv_orqs_preserved_non_parent_update; auto.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * apply upLockFreeInv_orqs_preserved_non_parent_update; auto.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr oidx) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }

        + find_if_inside.
          * apply upLockedInv_orqs_preserved_non_parent_update; auto.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * apply upLockFreeInv_orqs_preserved_non_parent_update; auto.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr oidx) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }

        + find_if_inside.
          * apply upLockedInv_orqs_preserved_non_parent_update; auto.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * apply upLockFreeInv_orqs_preserved_non_parent_update; auto.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr oidx) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }

      - (** case [RsBackRule] *)
        good_footprint_get (obj_idx obj).
        disc_rule_conds.

        + find_if_inside.
          * apply upLockedInv_orqs_preserved_non_parent_update; auto.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * apply upLockFreeInv_orqs_preserved_non_parent_update; auto.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr oidx) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }

        + rewrite <-H19 in H13.
          find_if_inside.
          * apply upLockedInv_orqs_preserved_non_parent_update; auto.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * apply upLockFreeInv_orqs_preserved_non_parent_update; auto.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr oidx) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }

        + rewrite <-H19 in H8.
          find_if_inside.
          * apply upLockedInv_orqs_preserved_non_parent_update; auto.
            apply upLockedInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * apply upLockFreeInv_orqs_preserved_non_parent_update; auto.
            apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
              [assumption| |].
            { destruct H.
              { remember (rqEdgeUpFrom dtr oidx) as orqUp.
                destruct orqUp; auto.
                eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }
            { destruct H.
              { remember (edgeDownTo dtr oidx) as odown.
                destruct odown; auto.
                eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
                dest; disc_rule_conds.
              }
              { destruct H as [rqUp [down [pidx ?]]]; dest.
                disc_rule_conds.
                solve_q.
              }
            }

      - (** case [RsDownRqDownRule] *)
        disc_rule_conds.
        find_if_inside.
        + apply upLockedInv_orqs_preserved_non_parent_update; auto.
          apply upLockedInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
          * destruct H as [rqUp [down [pidx ?]]]; dest.
            disc_rule_conds.
            solve_q.
        + apply upLockFreeInv_orqs_preserved_non_parent_update; auto.
          apply upLockFreeInv_msgs_preserved with (msgs1:= msgs);
            [assumption| |].
          * destruct H.
            { remember (rqEdgeUpFrom dtr oidx) as orqUp.
              destruct orqUp; auto.
              eapply eq_sym, rqEdgeUpFrom_Some in HeqorqUp; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
          * destruct H.
            { remember (edgeDownTo dtr oidx) as odown.
              destruct odown; auto.
              eapply eq_sym, edgeDownTo_Some in Heqodown; [|eassumption].
              dest; disc_rule_conds.
            }
            { destruct H as [rqUp [down [pidx ?]]]; dest.
              disc_rule_conds.
              solve_q.
            }
    Qed.
    
    Lemma upLockInv_step_int:
      UpLockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      UpLockInv {| bst_oss := (oss) +[ obj_idx obj <- nost];
                   bst_orqs := (orqs) +[ obj_idx obj <- norq];
                   bst_msgs := enqMsgs mouts (deqMsgs (idsOf mins) msgs) |}.
    Proof.
      intros.
      do 2 red; simpl; intros.
      good_rqrs_rule_get rule.
      specialize (H _ H0); simpl in H; dest.

      M.cmp (obj_idx obj) oidx; mred; simpl in *.
      - (** case [oidx = obj_idx obj] *)
        apply upLockInvORq_step_int_me; assumption.
      - (** case [oidx <> obj_idx obj] *)
        remember (parentIdxOf dtr oidx) as opidx.
        destruct opidx as [pidx|].
        + destruct (eq_nat_dec (obj_idx obj) pidx); subst.
          * apply upLockInvORq_step_int_parent; auto.
          * apply upLockInvORq_step_int_other; auto.
            rewrite <-Heqopidx.
            intro Hx; elim n0; inv Hx; reflexivity.
        + apply upLockInvORq_step_int_other; auto.
          rewrite <-Heqopidx; discriminate.
    Qed.

  End InternalStep.

  Lemma upLockInv_step:
    InvStep sys step_m UpLockInv.
  Proof.
    red; intros.
    inv H1.
    - auto.
    - apply upLockInv_step_ext_in; auto.
    - apply upLockInv_step_ext_out; auto.
    - eapply upLockInv_step_int; eauto.
      eapply footprints_ok; eassumption.
  Qed.

  Lemma upLockInv_ok:
    InvReachable sys step_m UpLockInv.
  Proof.
    apply inv_reachable.
    - apply upLockInv_init.
    - apply upLockInv_step.
  Qed.
  
End UpLockInv.

Close Scope list.
Close Scope fmap.
