Require Import Peano_dec Omega List ListSupport.
Require Import Common FMap.
Require Import Syntax Semantics SemFacts StepM Invariant Serial.
Require Import Reduction Commutativity QuasiSeq Topology.
Require Import RqRsTopo RqRsFacts RqRsInvMsg.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section DownLockInv.
  Context {oifc: OStateIfc}.
  Variables (dtr: DTree)
            (sys: System oifc).

  Hypotheses (Hrr: GoodRqRsSys dtr sys)
             (Hsd: RqRsDTree dtr sys)
             (Hers: GoodExtRssSys sys).

  Section OnMState.
    Variables (orqs: ORqs Msg)
              (msgs: MessagePool Msg).

    Definition ODownLockedTo (oidx: IdxT) (rsbTo: IdxT) :=
      orqs@[oidx] >>=[False]
          (fun orq =>
             exists rqi,
               orq@[downRq] = Some rqi /\
               rqi.(rqi_midx_rsb) = rsbTo).
    
    Definition ODownLockFree (oidx: IdxT) :=
      orqs@[oidx] >>=[True] (fun orq => DownLockFreeORq orq).

    Definition ONoDownLockTo (oidx: IdxT) (rsbTo: IdxT) :=
      orqs@[oidx] >>=[True]
          (fun orq =>
             match orq@[downRq] with
             | Some rqi => rqi.(rqi_midx_rsb) <> rsbTo
             | None => True
             end).

    Definition DownLockFreeChildInv (cidx: IdxT) (down rsUp: IdxT) :=
      rqsQ msgs down = nil /\
      findQ rsUp msgs = nil /\
      ONoDownLockTo cidx rsUp.
    
    Definition DownLockedChildInv (cidx: IdxT) (down rsUp: IdxT) :=
      length (rqsQ msgs down) <= 1 /\
      length (findQ rsUp msgs) <= 1 /\
      xor3 (length (rqsQ msgs down) = 1)
           (length (findQ rsUp msgs) = 1)
           (ODownLockedTo cidx rsUp).
    
    Definition DownLockFreeInv (oidx: IdxT) :=
      forall cidx,
        parentIdxOf dtr cidx = Some oidx ->
        exists down rsUp,
          edgeDownTo dtr cidx = Some down /\ 
          rsEdgeUpFrom dtr cidx = Some rsUp /\
          DownLockFreeChildInv cidx down rsUp.
    
    Definition DownLockedInv (oidx: IdxT) (rqi: RqInfo Msg) :=
      forall cidx,
        parentIdxOf dtr cidx = Some oidx ->
        exists down rsUp,
          edgeDownTo dtr cidx = Some down /\ 
          rsEdgeUpFrom dtr cidx = Some rsUp /\
          if in_dec eq_nat_dec rsUp rqi.(rqi_minds_rss)
          then DownLockedChildInv cidx down rsUp
          else DownLockFreeChildInv cidx down rsUp.

    Definition DownLockRssToParent (oidx: IdxT) (rqid: RqInfo Msg) :=
      Forall
        (fun rs =>
           exists cidx,
             parentIdxOf dtr cidx = Some oidx /\
             rsEdgeUpFrom dtr cidx = Some rs) rqid.(rqi_minds_rss).

    Definition DownLockInvORq (oidx: IdxT) (orq: ORq Msg) :=
      match orq@[downRq] with
      | Some rqid =>
        DownLockRssToParent oidx rqid /\ DownLockedInv oidx rqid
      | None => DownLockFreeInv oidx
      end.

    Definition DownLockInvMO :=
      forall oidx,
        In oidx (map (@obj_idx _) sys.(sys_objs)) ->
        let orq := orqs@[oidx] >>=[[]] (fun orq => orq) in
        DownLockInvORq oidx orq.

  End OnMState.
  
  Definition DownLockInv (st: MState oifc) :=
    DownLockInvMO st.(bst_orqs) st.(bst_msgs).

  Lemma downLockInv_init:
    InvInit sys DownLockInv.
  Proof.
    intros; do 3 red; cbn.
    intros; cbn.
    red; intros.
    eapply parentIdxOf_Some in H0; [|eassumption].
    destruct H0 as [rqUp [rsUp [down ?]]]; dest.
    exists down, rsUp; repeat split; assumption.
  Qed.

  Lemma downLockFreeChildInv_msgs_preserved:
    forall orqs msgs1 msgs2 cidx down rsUp,
      edgeDownTo dtr cidx = Some down ->
      rsEdgeUpFrom dtr cidx = Some rsUp ->
      DownLockFreeChildInv orqs msgs1 cidx down rsUp ->
      rqsQ msgs1 down = rqsQ msgs2 down ->
      findQ rsUp msgs1 = findQ rsUp msgs2 ->
      DownLockFreeChildInv orqs msgs2 cidx down rsUp.
  Proof.
    unfold DownLockFreeChildInv; intros.
    dest; rewrite <-H2, <-H3.
    split; [|split]; assumption.
  Qed.
    
  Lemma downLockedChildInv_msgs_preserved:
    forall orqs msgs1 msgs2 cidx down rsUp,
      edgeDownTo dtr cidx = Some down ->
      rsEdgeUpFrom dtr cidx = Some rsUp ->
      DownLockedChildInv orqs msgs1 cidx down rsUp ->
      rqsQ msgs1 down = rqsQ msgs2 down ->
      findQ rsUp msgs1 = findQ rsUp msgs2 ->
      DownLockedChildInv orqs msgs2 cidx down rsUp.
  Proof.
    unfold DownLockedChildInv; intros.
    dest; rewrite <-H2, <-H3.
    split; [|split]; assumption.
  Qed.

  Lemma downLockFreeInv_msgs_preserved:
    forall orqs msgs1 msgs2 oidx,
      DownLockFreeInv orqs msgs1 oidx ->
      (forall cidx down rsUp,
          parentIdxOf dtr cidx = Some oidx ->
          edgeDownTo dtr cidx = Some down ->
          rsEdgeUpFrom dtr cidx = Some rsUp ->
          rqsQ msgs1 down = rqsQ msgs2 down /\
          findQ rsUp msgs1 = findQ rsUp msgs2) ->
      DownLockFreeInv orqs msgs2 oidx.
  Proof.
    unfold DownLockFreeInv; simpl; intros.
    specialize (H _ H1).
    destruct H as [down [rsUp ?]]; dest.
    exists down, rsUp.
    split; [|split]; try assumption.
    specialize (H0 _ _ _ H1 H H2); dest.
    eapply downLockFreeChildInv_msgs_preserved; eauto.
  Qed.
  
  Lemma downLockFreeInv_disj_enqMsgs_preserved:
    forall orqs msgs emsgs oidx,
      DownLockFreeInv orqs msgs oidx ->
      SubList (idsOf emsgs) (sys_merqs sys) ->
      DownLockFreeInv orqs (enqMsgs emsgs msgs) oidx.
  Proof.
    intros.
    eapply downLockFreeInv_msgs_preserved; eauto.
    intros; split; intros.
    - unfold rqsQ.
      rewrite findQ_not_In_enqMsgs; [reflexivity|].
      intro Hx; apply H0 in Hx.
      apply Hsd in Hx; destruct Hx as [eoidx ?].
      solve_midx_false.
    - rewrite findQ_not_In_enqMsgs; [reflexivity|].
      intro Hx; apply H0 in Hx.
      apply Hsd in Hx; destruct Hx as [eoidx ?].
      solve_midx_false.
  Qed.

  Lemma downLockFreeInv_disj_deqMsgs_preserved:
    forall orqs msgs emsgs oidx,
      DownLockFreeInv orqs msgs oidx ->
      NoDup (idsOf emsgs) ->
      Forall (FirstMPI msgs) emsgs ->
      Forall (fun emsg => msg_type (valOf emsg) = MRs) emsgs ->
      SubList (idsOf emsgs) (sys_merss sys) ->
      DownLockFreeInv orqs (deqMsgs (idsOf emsgs) msgs) oidx.
  Proof.
    intros.
    eapply downLockFreeInv_msgs_preserved; eauto.
    intros; split; intros.
    - rewrite rqsQ_deqMsgs_rss; auto.
    - rewrite findQ_not_In_deqMsgs; [reflexivity|].
      intro Hx; apply H3 in Hx.
      apply Hsd in Hx; destruct Hx as [eoidx ?].
      solve_midx_false.
  Qed.
  
  Lemma downLockedInv_msgs_preserved:
    forall orqs msgs1 msgs2 oidx rqi,
      DownLockedInv orqs msgs1 oidx rqi ->
      (forall rsUp down cidx,
          parentIdxOf dtr cidx = Some oidx ->
          edgeDownTo dtr cidx = Some down ->
          rsEdgeUpFrom dtr cidx = Some rsUp ->
          rqsQ msgs1 down = rqsQ msgs2 down /\
          findQ rsUp msgs1 = findQ rsUp msgs2) ->
      DownLockedInv orqs msgs2 oidx rqi.
  Proof.
    unfold DownLockedInv; simpl; intros.
    specialize (H _ H1).
    destruct H as [down [rsUp ?]]; dest.
    specialize (H0 _ _ _ H1 H H2); dest.
    exists down, rsUp.
    split; [|split]; try assumption.
    find_if_inside.
    - eapply downLockedChildInv_msgs_preserved; eauto.
    - eapply downLockFreeChildInv_msgs_preserved; eauto.
  Qed.
  
  Corollary downLockedInv_disj_enqMsgs_preserved:
    forall orqs msgs emsgs oidx rqi,
      DownLockedInv orqs msgs oidx rqi ->
      SubList (idsOf emsgs) (sys_merqs sys) ->
      DownLockedInv orqs (enqMsgs emsgs msgs) oidx rqi.
  Proof.
    intros.
    eapply downLockedInv_msgs_preserved; eauto.
    intros; split.
    - unfold rqsQ.
      rewrite findQ_not_In_enqMsgs; [reflexivity|].
      intro Hx; apply H0 in Hx.
      apply Hsd in Hx; destruct Hx as [eoidx ?].
      solve_midx_false.
    - rewrite findQ_not_In_enqMsgs; [reflexivity|].
      intro Hx; apply H0 in Hx.
      apply Hsd in Hx; destruct Hx as [eoidx ?].
      solve_midx_false.
  Qed.

  Lemma downLockedInv_disj_deqMsgs_preserved:
    forall orqs msgs emsgs oidx rqi,
      DownLockedInv orqs msgs oidx rqi ->
      NoDup (idsOf emsgs) ->
      Forall (FirstMPI msgs) emsgs ->
      Forall (fun emsg => msg_type (valOf emsg) = MRs) emsgs ->
      SubList (idsOf emsgs) (sys_merss sys) ->
      DownLockedInv orqs (deqMsgs (idsOf emsgs) msgs) oidx rqi.
  Proof.
    intros.
    eapply downLockedInv_msgs_preserved; eauto.
    intros; split.
    - rewrite rqsQ_deqMsgs_rss; auto.
    - rewrite findQ_not_In_deqMsgs; [reflexivity|].
      intro Hx; apply H3 in Hx.
      apply Hsd in Hx; destruct Hx as [eoidx ?].
      solve_midx_false.
  Qed.
  
  Lemma downLockedChildInv_orqs_preserved_not_child_update:
    forall orqs msgs cidx down rsUp oidx orq ooidx,
      parentIdxOf dtr cidx = Some oidx ->
      DownLockedChildInv orqs msgs cidx down rsUp ->
      ooidx <> cidx ->
      DownLockedChildInv (orqs+[ooidx <- orq]) msgs cidx down rsUp.
  Proof.
    intros.
    red in H0; dest.
    repeat split; try assumption.
    unfold ODownLockedTo in *.
    mred.
  Qed.

  Lemma downLockedChildInv_orqs_preserved_downRq_intact:
    forall orqs msgs cidx down rsUp oidx porq norq,
      parentIdxOf dtr cidx = Some oidx ->
      DownLockedChildInv orqs msgs cidx down rsUp ->
      orqs@[cidx] = Some porq ->
      porq@[downRq] = norq@[downRq] ->
      DownLockedChildInv (orqs+[cidx <- norq]) msgs cidx down rsUp.
  Proof.
    intros.
    red in H0; dest.
    repeat split; try assumption.
    unfold ODownLockedTo in *.
    inv H4.
    - xfst; try assumption.
      mred; simpl; rewrite <-H2; assumption.
    - xsnd; try assumption.
      mred; simpl; rewrite <-H2; assumption.
    - xthd; try assumption.
      mred; simpl; rewrite <-H2; assumption.
  Qed.

  Lemma downLockedChildInv_orqs_preserved_downRq_rsbTo_1:
    forall orqs msgs cidx down rsUp oidx porq norq rqid,
      parentIdxOf dtr cidx = Some oidx ->
      DownLockedChildInv orqs msgs cidx down rsUp ->
      orqs@[cidx] = Some porq ->
      porq@[downRq] = None ->
      norq@[downRq] = Some rqid ->
      rqid.(rqi_midx_rsb) <> rsUp ->
      DownLockedChildInv (orqs+[cidx <- norq]) msgs cidx down rsUp.
  Proof.
    intros.
    red in H0; dest.
    repeat split; try assumption.
    unfold ODownLockedTo in *.
    inv H6.
    - xfst; try assumption.
      mred; simpl.
      intro Hx; destruct Hx as [rqi ?]; dest.
      rewrite H3 in H6; inv H6; auto.
    - xsnd; try assumption.
      mred; simpl.
      intro Hx; destruct Hx as [rqi ?]; dest.
      rewrite H3 in H6; inv H6; auto.
    - xthd; try assumption.
      mred; simpl.
      destruct H9 as [rqi ?]; dest; discriminate.
  Qed.

  Lemma downLockedChildInv_orqs_preserved_downRq_rsbTo_2:
    forall orqs msgs cidx down rsUp oidx porq norq rqid,
      parentIdxOf dtr cidx = Some oidx ->
      DownLockedChildInv orqs msgs cidx down rsUp ->
      orqs@[cidx] = Some porq ->
      porq@[downRq] = Some rqid ->
      rqid.(rqi_midx_rsb) <> rsUp ->
      norq@[downRq] = None ->
      DownLockedChildInv (orqs+[cidx <- norq]) msgs cidx down rsUp.
  Proof.
    intros.
    red in H0; dest.
    repeat split; try assumption.
    unfold ODownLockedTo in *.
    inv H6.
    - xfst; try assumption.
      mred; simpl.
      intro Hx; destruct Hx as [rqi ?]; dest.
      congruence.
    - xsnd; try assumption.
      mred; simpl.
      intro Hx; destruct Hx as [rqi ?]; dest.
      congruence.
    - xthd; try assumption.
      mred; simpl.
      destruct H9 as [rqi ?]; dest.
      inv H6; elim H3; reflexivity.
  Qed.

  Lemma downLockFreeChildInv_orqs_preserved_not_child_update:
    forall orqs msgs cidx down rsUp oidx orq ooidx,
      parentIdxOf dtr cidx = Some oidx ->
      DownLockFreeChildInv orqs msgs cidx down rsUp ->
      ooidx <> cidx ->
      DownLockFreeChildInv (orqs+[ooidx <- orq]) msgs cidx down rsUp.
  Proof.
    intros.
    red in H0; dest.
    repeat split; try assumption.
    unfold ONoDownLockTo in *.
    mred.
  Qed.
  
  Lemma downLockFreeChildInv_orqs_preserved_downRq_intact:
    forall orqs msgs cidx down rsUp oidx porq norq,
      parentIdxOf dtr cidx = Some oidx ->
      DownLockFreeChildInv orqs msgs cidx down rsUp ->
      orqs@[cidx] = Some porq ->
      porq@[downRq] = norq@[downRq] ->
      DownLockFreeChildInv (orqs+[cidx <- norq]) msgs cidx down rsUp.
  Proof.
    intros.
    red in H0; dest.
    repeat split; try assumption.
    unfold ONoDownLockTo in *.
    mred; simpl; rewrite <-H2; assumption.
  Qed.

  Lemma downLockFreeChildInv_orqs_preserved_downRq_rsbTo_1:
    forall orqs msgs cidx down rsUp oidx norq rqid,
      parentIdxOf dtr cidx = Some oidx ->
      DownLockFreeChildInv orqs msgs cidx down rsUp ->
      norq@[downRq] = Some rqid ->
      rqid.(rqi_midx_rsb) <> rsUp ->
      DownLockFreeChildInv (orqs+[cidx <- norq]) msgs cidx down rsUp.
  Proof.
    intros.
    red in H0; dest.
    repeat split; try assumption.
    red; mred; simpl.
    rewrite H1; assumption.
  Qed.

  Lemma downLockFreeChildInv_orqs_preserved_downRq_rsbTo_2:
    forall orqs msgs cidx down rsUp oidx norq,
      parentIdxOf dtr cidx = Some oidx ->
      DownLockFreeChildInv orqs msgs cidx down rsUp ->
      norq@[downRq] = None ->
      DownLockFreeChildInv (orqs+[cidx <- norq]) msgs cidx down rsUp.
  Proof.
    intros.
    red in H0; dest.
    repeat split; try assumption.
    red; mred; simpl.
    rewrite H1; auto.
  Qed.

  Lemma downLockedInv_orqs_preserved_self_update:
    forall orqs msgs oidx orq rqid,
      DownLockedInv orqs msgs oidx rqid ->
      DownLockedInv (orqs+[oidx <- orq]) msgs oidx rqid.
  Proof.
    intros.
    red in H; red; intros.
    specialize (H _ H0).
    destruct H as [down [rsUp ?]]; dest.
    exists down, rsUp.
    repeat split; try assumption.
    find_if_inside.
    - eapply downLockedChildInv_orqs_preserved_not_child_update; eauto.
      intro Hx; subst; apply parentIdxOf_not_eq in H0; [|apply Hsd]; auto.
    - eapply downLockFreeChildInv_orqs_preserved_not_child_update; eauto.
      intro Hx; subst; apply parentIdxOf_not_eq in H0; [|apply Hsd]; auto.
  Qed.

  Lemma downLockedInv_orqs_preserved_not_child_update:
    forall orqs msgs oidx orq rqid ooidx ,
      DownLockedInv orqs msgs oidx rqid ->
      parentIdxOf dtr ooidx <> Some oidx ->
      DownLockedInv (orqs+[ooidx <- orq]) msgs oidx rqid.
  Proof.
    intros.
    red in H; red; intros.
    specialize (H _ H1).
    destruct H as [down [rsUp ?]]; dest.
    exists down, rsUp.
    repeat split; try assumption.
    find_if_inside.
    - eapply downLockedChildInv_orqs_preserved_not_child_update; eauto.
      intro Hx; subst; auto.
    - eapply downLockFreeChildInv_orqs_preserved_not_child_update; eauto.
      intro Hx; subst; auto.
  Qed.

  Lemma downLockedInv_orqs_preserved_downRq_intact:
    forall orqs msgs oidx rqid cidx porq norq,
      parentIdxOf dtr cidx = Some oidx ->
      DownLockedInv orqs msgs oidx rqid ->
      orqs@[cidx] = Some porq ->
      porq@[downRq] = norq@[downRq] ->
      DownLockedInv (orqs+[cidx <- norq]) msgs oidx rqid.
  Proof.
    intros.
    red in H0; red; intros.
    specialize (H0 _ H3).
    destruct H0 as [cdown [crsUp ?]]; dest.
    exists cdown, crsUp.
    repeat split; try assumption.
    destruct (eq_nat_dec cidx cidx0); subst.
    - find_if_inside.
      + repeat disc_rule_minds.
        eapply downLockedChildInv_orqs_preserved_downRq_intact; eauto.
      + repeat disc_rule_minds.
        eapply downLockFreeChildInv_orqs_preserved_downRq_intact; eauto.
    - find_if_inside.
      + eapply downLockedChildInv_orqs_preserved_not_child_update; eauto.
      + eapply downLockFreeChildInv_orqs_preserved_not_child_update; eauto.
  Qed.
  
  Lemma downLockedInv_orqs_preserved_downRq_rsbTo_1:
    forall orqs msgs oidx rqid rqi cidx porq norq rsUp,
      parentIdxOf dtr cidx = Some oidx ->
      rsEdgeUpFrom dtr cidx = Some rsUp ->
      DownLockedInv orqs msgs oidx rqid ->
      orqs@[cidx] = Some porq ->
      porq@[downRq] = None ->
      norq@[downRq] = Some rqi ->
      rqi.(rqi_midx_rsb) <> rsUp ->
      DownLockedInv (orqs+[cidx <- norq]) msgs oidx rqid.
  Proof.
    intros.
    red in H1; red; intros.
    specialize (H1 _ H6).
    destruct H1 as [cdown [crsUp ?]]; dest.
    exists cdown, crsUp.
    repeat split; try assumption.
    destruct (eq_nat_dec cidx cidx0); subst.
    - find_if_inside.
      + repeat disc_rule_minds.
        eapply downLockedChildInv_orqs_preserved_downRq_rsbTo_1; eauto.
      + repeat disc_rule_minds.
        eapply downLockFreeChildInv_orqs_preserved_downRq_rsbTo_1; eauto.
    - find_if_inside.
      + eapply downLockedChildInv_orqs_preserved_not_child_update; eauto.
      + eapply downLockFreeChildInv_orqs_preserved_not_child_update; eauto.
  Qed.

  Lemma downLockedInv_orqs_preserved_downRq_rsbTo_2:
    forall orqs msgs oidx rqid rqi cidx porq norq rsUp,
      parentIdxOf dtr cidx = Some oidx ->
      rsEdgeUpFrom dtr cidx = Some rsUp ->
      DownLockedInv orqs msgs oidx rqid ->
      orqs@[cidx] = Some porq ->
      porq@[downRq] = Some rqi ->
      rqi.(rqi_midx_rsb) <> rsUp ->
      norq@[downRq] = None ->
      DownLockedInv (orqs+[cidx <- norq]) msgs oidx rqid.
  Proof.
    intros.
    red in H1; red; intros.
    specialize (H1 _ H6).
    destruct H1 as [cdown [crsUp ?]]; dest.
    exists cdown, crsUp.
    repeat split; try assumption.
    destruct (eq_nat_dec cidx cidx0); subst.
    - find_if_inside.
      + repeat disc_rule_minds.
        eapply downLockedChildInv_orqs_preserved_downRq_rsbTo_2; eauto.
      + repeat disc_rule_minds.
        eapply downLockFreeChildInv_orqs_preserved_downRq_rsbTo_2; eauto.
    - find_if_inside.
      + eapply downLockedChildInv_orqs_preserved_not_child_update; eauto.
      + eapply downLockFreeChildInv_orqs_preserved_not_child_update; eauto.
  Qed.

  Lemma downLockFreeInv_orqs_preserved_self_update:
    forall orqs msgs oidx orq,
      DownLockFreeInv orqs msgs oidx ->
      DownLockFreeInv (orqs+[oidx <- orq]) msgs oidx.
  Proof.
    intros.
    red in H; red; intros.
    specialize (H _ H0).
    destruct H as [down [rsUp ?]]; dest.
    exists down, rsUp.
    split; [|split]; try assumption.
    eapply downLockFreeChildInv_orqs_preserved_not_child_update; eauto.
    intro Hx; subst; apply parentIdxOf_not_eq in H0; [|apply Hsd]; auto.
  Qed.

  Lemma downLockFreeInv_orqs_preserved_not_child_update:
    forall orqs msgs oidx orq ooidx,
      DownLockFreeInv orqs msgs oidx ->
      parentIdxOf dtr ooidx <> Some oidx ->
      DownLockFreeInv (orqs+[ooidx <- orq]) msgs oidx.
  Proof.
    intros.
    red in H; red; intros.
    specialize (H _ H1).
    destruct H as [down [rsUp ?]]; dest.
    exists down, rsUp.
    split; [|split]; try assumption.
    eapply downLockFreeChildInv_orqs_preserved_not_child_update; eauto.
    intro Hx; subst; auto.
  Qed.

  Lemma downLockFreeInv_orqs_preserved_downRq_intact:
    forall orqs msgs oidx cidx porq norq,
      parentIdxOf dtr cidx = Some oidx ->
      DownLockFreeInv orqs msgs oidx ->
      orqs@[cidx] = Some porq ->
      porq@[downRq] = norq@[downRq] ->
      DownLockFreeInv (orqs+[cidx <- norq]) msgs oidx.
  Proof.
    intros.
    red in H0; red; intros.
    specialize (H0 _ H3).
    destruct H0 as [cdown [crsUp ?]]; dest.
    exists cdown, crsUp.
    split; [|split]; try assumption.
    destruct (eq_nat_dec cidx cidx0); subst.
    - repeat disc_rule_minds.
      eapply downLockFreeChildInv_orqs_preserved_downRq_intact; eauto.
    - eapply downLockFreeChildInv_orqs_preserved_not_child_update; eauto.
  Qed.
  
  Lemma downLockFreeInv_orqs_preserved_downRq_rsbTo_1:
    forall orqs msgs oidx rqid cidx norq rsUp,
      parentIdxOf dtr cidx = Some oidx ->
      rsEdgeUpFrom dtr cidx = Some rsUp ->
      DownLockFreeInv orqs msgs oidx ->
      norq@[downRq] = Some rqid ->
      rqid.(rqi_midx_rsb) <> rsUp ->
      DownLockFreeInv (orqs+[cidx <- norq]) msgs oidx.
  Proof.
    intros.
    red in H1; red; intros.
    specialize (H1 _ H4).
    destruct H1 as [cdown [crsUp ?]]; dest.
    exists cdown, crsUp.
    split; [|split]; try assumption.
    destruct (eq_nat_dec cidx cidx0); subst.
    - repeat disc_rule_minds.
      eapply downLockFreeChildInv_orqs_preserved_downRq_rsbTo_1; eauto.
    - eapply downLockFreeChildInv_orqs_preserved_not_child_update; eauto.
  Qed.

  Lemma downLockFreeInv_orqs_preserved_downRq_rsbTo_2:
    forall orqs msgs oidx cidx norq rsUp,
      parentIdxOf dtr cidx = Some oidx ->
      rsEdgeUpFrom dtr cidx = Some rsUp ->
      DownLockFreeInv orqs msgs oidx ->
      norq@[downRq] = None ->
      DownLockFreeInv (orqs+[cidx <- norq]) msgs oidx.
  Proof.
    intros.
    red in H1; red; intros.
    specialize (H1 _ H3).
    destruct H1 as [cdown [crsUp ?]]; dest.
    exists cdown, crsUp.
    split; [|split]; try assumption.
    destruct (eq_nat_dec cidx cidx0); subst.
    - repeat disc_rule_minds.
      eapply downLockFreeChildInv_orqs_preserved_downRq_rsbTo_2; eauto.
    - eapply downLockFreeChildInv_orqs_preserved_not_child_update; eauto.
  Qed.
  
  Lemma downLockedChildInv_requested:
    forall oidx cidx down rsUp porq P orqs msgs mouts rqi,
      parentIdxOf dtr cidx = Some oidx ->
      edgeDownTo dtr cidx = Some down ->
      rsEdgeUpFrom dtr cidx = Some rsUp ->
      DownLockFreeChildInv orqs msgs cidx down rsUp ->
      In rsUp (rqi_minds_rss rqi) ->      
      NoDup (idsOf mouts) ->
      Forall (fun idm => msg_type (valOf idm) = MRq) mouts ->
      RqRsDownMatch dtr oidx (idsOf mouts) (rqi_minds_rss rqi) P ->
      DownLockedChildInv (orqs +[oidx <- porq +[ downRq <- rqi]])
                         (enqMsgs mouts msgs) cidx down rsUp.
  Proof.
    intros; destruct Hsd as [? [? _]].
    red in H2; dest; red.

    assert (length (rqsQ (enqMsgs mouts msgs) down) = 1).
    { eapply RqRsDownMatch_rs_rq in H6; eauto.
      destruct H6 as [rcidx [rdown ?]]; dest.
      repeat disc_rule_minds.
      apply in_map_iff in H14.
      destruct H14 as [[midx msg] ?]; dest; simpl in *; subst.
      rewrite Forall_forall in H5.
      specialize (H5 _ H12); simpl in H5.
      unfold rqsQ.
      erewrite findQ_In_NoDup_enqMsgs; eauto.
      rewrite filter_app; simpl.
      rewrite H5; simpl.
      unfold rqsQ in H2; rewrite H2.
      reflexivity.
    }

    assert (length (findQ rsUp (enqMsgs mouts msgs)) = 0).
    { solve_q; rewrite H9; reflexivity. }

    rewrite H11, H12.
    repeat split; try omega.
    xfst; [reflexivity|discriminate|].

    apply parentIdxOf_not_eq in H; [|assumption].
    intro Hx; red in H10, Hx.
    mred.
    destruct (orqs@[cidx]) as [corq|]; auto.
    simpl in H10, Hx.
    destruct Hx as [crqi [? ?]].
    rewrite H13 in H10; auto.
  Qed.

  Lemma downLockedInv_requested:
    forall orqs msgs oidx mouts P rqi porq,
      DownLockFreeInv orqs msgs oidx ->
      RqRsDownMatch dtr oidx (idsOf mouts) (rqi_minds_rss rqi) P ->
      NoDup (idsOf mouts) ->
      Forall (fun idm : Id Msg => msg_type (valOf idm) = MRq) mouts ->
      DownLockedInv (orqs +[oidx <- porq +[downRq <- rqi]])
                    (enqMsgs mouts msgs) oidx rqi.
  Proof.
    intros.
    red in H; red; intros.
    specialize (H _ H3).
    destruct H as [down [rsUp ?]]; dest.
    exists down, rsUp.
    repeat split; try assumption.
    find_if_inside.
    * eapply downLockedChildInv_requested; try eassumption.
    * eapply downLockFreeChildInv_orqs_preserved_not_child_update; eauto.
      { eapply downLockFreeChildInv_msgs_preserved; try eassumption; solve_q. }
      { intro Hx; subst; apply parentIdxOf_not_eq in H3; [|apply Hsd]; auto. }
  Qed.

  Lemma downLockFreeChildInv_responded:
    forall orqs msgs oidx rqi mins rqTos P porq,
      DownLockedInv orqs msgs oidx rqi ->
      NoDup (idsOf mins) ->
      Forall (FirstMPI msgs) mins ->
      Forall (fun idm => msg_type (valOf idm) = MRs) mins ->
      RqRsDownMatch dtr oidx rqTos (idsOf mins) P ->
      idsOf mins = rqi.(rqi_minds_rss) ->
      DownLockFreeInv (orqs +[oidx <- porq -[downRq]])
                      (deqMsgs (idsOf mins) msgs) oidx.
  Proof.
    intros.
    apply downLockFreeInv_orqs_preserved_self_update.

    red in H; red; intros.
    specialize (H _ H5).
    destruct H as [down [rsUp ?]]; dest.
    exists down, rsUp.
    split; [|split]; try assumption.

    find_if_inside.
    - red in H7; dest.
      rewrite <-H4 in i; apply in_map_iff in i.
      destruct i as [[rsUp' rsum] [? ?]]; simpl in *; subst.
      pose proof H1.
      rewrite Forall_forall in H10.
      specialize (H10 _ H11).
      assert (length (findQ rsUp msgs) = 1) by (eapply findQ_length_one; eauto).
      eapply xor3_inv_2 with (B:= length (findQ rsUp msgs) = 1) in H9;
        [dest|assumption].
      red; split; [|split].
      { rewrite rqsQ_deqMsgs_rss; try assumption.
        destruct (rqsQ msgs down); [reflexivity|simpl in *; omega].
      }
      { apply in_map with (f:= idOf) in H11; simpl in H11.
        assert (findQ rsUp msgs <> nil) by (destruct (findQ rsUp msgs); discriminate).
        eapply findQ_In_NoDup_deqMsgs in H14; try eassumption.
        destruct H14 as [dmsg ?].
        rewrite <-H14 in H12.
        destruct (findQ rsUp (deqMsgs _ _)); [reflexivity|discriminate].
      }
      { unfold ODownLockedTo in H13.
        red; destruct (orqs@[cidx]) as [corq|]; simpl in *; auto.
        destruct (corq@[downRq]) as [crqi|]; auto.
        intro Hx; elim H13; eauto.
      }
    - eapply downLockFreeChildInv_msgs_preserved; try eassumption.
      + solve_q.
      + rewrite findQ_not_In_deqMsgs; auto.
        rewrite H4; assumption.
  Qed.
  
  Lemma downLockInv_step_ext_in:
    forall oss orqs msgs eins,
      DownLockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eins <> nil ->
      ValidMsgsExtIn sys eins ->
      DownLockInv {| bst_oss := oss;
                     bst_orqs := orqs;
                     bst_msgs := enqMsgs eins msgs |}.
  Proof.
    unfold DownLockInv; simpl; intros.
    red; intros.
    specialize (H oidx H2).
    destruct H1.
    destruct (orqs@[oidx]) as [orq|]; simpl in *; dest.
    - red in H; red.
      remember (orq@[downRq]) as orqi.
      destruct orqi as [rqi|].
      + dest; split; [assumption|].
        apply downLockedInv_disj_enqMsgs_preserved; assumption.
      + apply downLockFreeInv_disj_enqMsgs_preserved; assumption.
    - apply downLockFreeInv_disj_enqMsgs_preserved; assumption.
  Qed.

  Lemma downLockInv_step_ext_out:
    forall oss orqs msgs eouts,
      DownLockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      eouts <> nil ->
      Forall (FirstMPI msgs) eouts ->
      ValidMsgsExtOut sys eouts ->
      Forall (fun emsg : Id Msg => msg_type (valOf emsg) = MRs) eouts ->
      DownLockInv {| bst_oss := oss;
                     bst_orqs := orqs;
                     bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    unfold DownLockInv; simpl; intros.
    red; intros.
    specialize (H oidx H4).
    destruct H2.
    destruct (orqs@[oidx]) as [orq|]; simpl in *; dest.
    - red in H; red.
      remember (orq@[downRq]) as orqi.
      destruct orqi as [rqi|].
      + dest; split; [assumption|].
        apply downLockedInv_disj_deqMsgs_preserved; try assumption.
      + apply downLockFreeInv_disj_deqMsgs_preserved; assumption.
    - apply downLockFreeInv_disj_deqMsgs_preserved; assumption.
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

    Lemma downLockInvORq_step_int_me:
      DownLockInvORq orqs msgs (obj_idx obj) porq ->
      In (obj_idx obj) (map (@obj_idx _) (sys_objs sys)) ->
      GoodRqRsRule dtr sys (obj_idx obj) rule ->
      DownLockInvORq (orqs+[obj_idx obj <- norq])
                     (enqMsgs mouts (deqMsgs (idsOf mins) msgs))
                     (obj_idx obj) norq.
    Proof.
      intros.
      destruct Hsd as [? [? _]].
      red in H; red.
      good_rqrs_rule_cases rule.

      - (** case [ImmDownRule] *)
        disc_rule_conds.
        apply downLockFreeInv_orqs_preserved_self_update.
        eapply downLockFreeInv_msgs_preserved; eauto.
        intros; split; intros.
        + rewrite rqsQ_enqMP_rs by assumption.
          solve_q.
        + solve_q.

      - (** case [ImmUpRule] *)
        disc_rule_conds.
        apply downLockFreeInv_orqs_preserved_self_update.
        eapply downLockFreeInv_msgs_preserved; eauto.
        intros; split; intros; solve_q.

      - (** case [RqFwdRule] *)
        disc_rule_conds.
        + (** case [RqUpUp] *)
          destruct (porq@[downRq]) as [rqid|].
          * dest; split; [assumption|].
            apply downLockedInv_orqs_preserved_self_update.
            eapply downLockedInv_msgs_preserved; eauto.
            intros; split; intros; solve_q.
          * apply downLockFreeInv_orqs_preserved_self_update.
            eapply downLockFreeInv_msgs_preserved; eauto.
            intros; split; intros; solve_q.
        + (** case [RqUpDown] *)
          split.
          * apply Forall_forall; intros rsFrom ?.
            eapply RqRsDownMatch_rs_rq in H10; [|eassumption].
            dest; eauto.
          * destruct HmoutsV.
            eapply downLockedInv_requested; eauto.
            eapply downLockFreeInv_msgs_preserved; [eassumption|].
            intros; split; solve_q.
        + (** case [RqDownDown] *)
          destruct HmoutsV.
          split.
          * apply Forall_forall; intros rsFrom ?.
            eapply RqRsDownMatch_rs_rq in H5; [|eassumption].
            dest; eauto.
          * eapply downLockedInv_requested; eauto.
            eapply downLockFreeInv_msgs_preserved; [eassumption|].
            intros; split; solve_q.

      - (** case [RsBackRule] *)
        good_footprint_get (obj_idx obj).
        disc_rule_conds.
        + (** case [RsDownDown] *)
          apply downLockFreeInv_orqs_preserved_self_update.
          eapply downLockFreeInv_msgs_preserved; eauto.
          intros; split; intros.
          * rewrite rqsQ_enqMP_rs by assumption.
            solve_q.
          * solve_q.
        + (** case [RsUp(Down)] *)
          eapply downLockFreeInv_msgs_preserved.
          * destruct HminsV.
            rewrite <-H18 in H12.
            eapply downLockFreeChildInv_responded; eauto.
          * intros; split.
            { rewrite rqsQ_enqMP_rs; [reflexivity|assumption]. }
            { solve_q. }
        + (** case [RsUp(Up)] *)
          eapply downLockFreeInv_msgs_preserved.
          * destruct HminsV.
            rewrite <-H18 in H6.
            eapply downLockFreeChildInv_responded; eauto.
          * intros; split.
            { rewrite rqsQ_enqMP_rs; [reflexivity|assumption]. }
            { solve_q. }

      - (** case [RsDownRqDownRule] *)
        disc_rule_conds.
        split.
        + apply Forall_forall; intros rrsFrom ?.
          eapply RqRsDownMatch_rs_rq in H11; [|eassumption].
          dest; eauto.
        + destruct HmoutsV.
          eapply downLockedInv_requested; eauto.
          eapply downLockFreeInv_msgs_preserved; [eassumption|].
          intros; split; solve_q.
    Qed.

    Lemma downLockInvORq_step_int_child:
      forall oidx,
        DownLockInvORq orqs msgs oidx ((orqs@[oidx]) >>=[[]] (fun orq => orq)) ->
        In oidx (map (@obj_idx _) (sys_objs sys)) ->
        GoodRqRsRule dtr sys (obj_idx obj) rule ->
        parentIdxOf dtr (obj_idx obj) = Some oidx ->
        DownLockInvORq (orqs+[obj_idx obj <- norq])
                     (enqMsgs mouts (deqMsgs (idsOf mins) msgs)) oidx
                     ((orqs@[ oidx]) >>=[[]] (fun orq => orq)).
    Proof.
      intros.
      destruct Hsd as [? [? _]].
      red in H; red.
      good_rqrs_rule_cases rule.

      - (** case [ImmDownRule] *)
        disc_rule_conds.
        replace (orqs +[obj_idx obj <- norq]) with orqs by meq.
        destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
        + dest; split; [assumption|].
          eapply downLockedInv_msgs_preserved; [eassumption|].
          intros; split.
          * rewrite rqsQ_enqMP_rs by assumption; solve_q.
          * solve_q.
        + eapply downLockFreeInv_msgs_preserved; [eassumption|].
          intros; split.
          * rewrite rqsQ_enqMP_rs by assumption; solve_q.
          * solve_q.

      - (** case [ImmUpRule] *)
        disc_rule_conds.
        replace (orqs +[obj_idx obj <- norq]) with orqs by meq.
        destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
        + dest; split; [assumption|].
          pose proof (H1 _ H2).
          destruct H5 as [odown [orsUp ?]]; dest.
          repeat disc_rule_minds.
          red in H1; red; intros.
          specialize (H1 _ H5).
          destruct H1 as [down [rsUp ?]]; dest.
          exists down, rsUp; repeat split; try assumption.
          destruct (eq_nat_dec cidx (obj_idx obj)); subst.
          * repeat disc_rule_minds.
            clear H10; find_if_inside.
            { red in H12; red; dest.
              xor3_inv1 H12; [dest|eapply rqsQ_length_one; eauto].
              replace (length (rqsQ (enqMP orsUp rsm (deqMP odown msgs)) odown)) with 0;
                [|solve_q;
                  apply rqsQ_length_zero in H11; try assumption;
                  simpl in H11; unfold rqsQ in H11; rewrite H11; reflexivity].
              replace (length (findQ orsUp (enqMP orsUp rsm (deqMP odown msgs)))) with 1;
                [|solve_q; destruct (findQ orsUp msgs); simpl in *; omega].
              repeat split; try omega.
              xsnd; [omega|omega|assumption].
            }
            { exfalso; red in H12; dest.
              eapply rqsQ_length_zero_False; eauto.
            }
          * clear H10; find_if_inside.
            { eapply downLockedChildInv_msgs_preserved; eauto; solve_q. }
            { eapply downLockFreeChildInv_msgs_preserved; eauto; solve_q. }
        + exfalso; specialize (H _ H2).
          destruct H as [odown [orsUp ?]]; dest.
          repeat disc_rule_minds.
          red in H5; dest.
          eapply rqsQ_length_zero_False; eauto.

      - (** case [RqFwdRule] *)
        disc_rule_conds.
        + (** [RqUpUp] *)
          destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
          * dest; split; [assumption|].
            eapply downLockedInv_orqs_preserved_downRq_intact; eauto; [|mred].
            eapply downLockedInv_msgs_preserved; [eassumption|].
            intros; split; solve_q.
          * eapply downLockFreeInv_orqs_preserved_downRq_intact; eauto; [|mred].
            eapply downLockFreeInv_msgs_preserved; [eassumption|].
            intros; split; solve_q.
        + (** [RqUpDown] *)
          pose proof H2.
          eapply parentIdxOf_Some in H5; [|eassumption].
          destruct H5 as [rqUp [rsUp [down ?]]]; dest.
          assert (Some oidx <> Some (obj_idx obj)).
          { intro Hx; inv Hx; apply parentIdxOf_not_eq in H2; auto. }
          destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
          * dest; split; [assumption|].
            eapply downLockedInv_orqs_preserved_downRq_rsbTo_1; try eassumption.
            { eapply downLockedInv_msgs_preserved; [eassumption|].
              intros; split; solve_q.
            }
            { mred. }
            { solve_midx_neq. }
          * eapply downLockFreeInv_orqs_preserved_downRq_rsbTo_1; try eassumption.
            { eapply downLockFreeInv_msgs_preserved; [eassumption|].
              intros; split; solve_q.
            }
            { mred. }
            { solve_midx_neq. }
        + (** [RqDownDown] *)
          destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
          * dest; split; [assumption|].
            pose proof (H7 _ H2).
            destruct H9 as [odown [orsUp ?]]; dest.
            repeat disc_rule_minds.
            red in H7; red; intros.
            specialize (H7 _ H9).
            destruct H7 as [down [rsUp ?]]; dest.
            exists down, rsUp; repeat split; try assumption.
            destruct (eq_nat_dec cidx (obj_idx obj)); subst.
            { repeat disc_rule_minds.
              clear H15; find_if_inside.
              { red in H16; red; dest.
                xor3_inv1 H9; [dest|eapply rqsQ_length_one; eauto].
                replace (length (rqsQ (enqMsgs mouts (deqMP odown msgs)) odown)) with 0;
                  [|solve_q;
                    apply rqsQ_length_zero in H14; try assumption;
                    simpl in H14; unfold rqsQ in H14; rewrite H14; reflexivity].
                replace (length (findQ (rqi_midx_rsb rqi) (enqMsgs mouts (deqMP odown msgs))))
                  with 0; [|solve_q;
                            destruct (findQ (rqi_midx_rsb rqi) msgs);
                            simpl in *; omega].
                repeat split; try omega.
                xthd; [omega|omega|].
                red; mred; simpl.
                exists rqi; split; [mred|reflexivity].
              }
              { exfalso; red in H16; dest.
                eapply rqsQ_length_zero_False; eauto.
              }
            }
            { assert (Some oidx <> Some (obj_idx obj)).
              { intro Hx; inv Hx; apply parentIdxOf_not_eq in H2; auto. }
              clear H15; find_if_inside.
              { eapply downLockedChildInv_orqs_preserved_not_child_update; eauto.
                eapply downLockedChildInv_msgs_preserved; eauto; solve_q.
              }
              { eapply downLockFreeChildInv_orqs_preserved_not_child_update; eauto.
                eapply downLockFreeChildInv_msgs_preserved; eauto; solve_q.
              }
            }
          * exfalso; specialize (H _ H2).
            destruct H as [odown [orsUp ?]]; dest.
            repeat disc_rule_minds.
            red in H9; dest.
            eapply rqsQ_length_zero_False; eauto.

      - (** case [RsBackRule] *)
        good_footprint_get (obj_idx obj).
        disc_rule_conds.
        + (** [RsDownDown] *)
          destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
          * dest; split; [assumption|].
            eapply downLockedInv_orqs_preserved_downRq_intact; eauto; [|mred].
            eapply downLockedInv_msgs_preserved; [eassumption|].
            intros; split.
            { rewrite rqsQ_enqMP_rs by assumption.
              erewrite rqsQ_deqMP_rs by eassumption.
              reflexivity.
            }
            { solve_q. }
          * eapply downLockFreeInv_orqs_preserved_downRq_intact; eauto; [|mred].
            eapply downLockFreeInv_msgs_preserved; [eassumption|].
            intros; split.
            { rewrite rqsQ_enqMP_rs by assumption.
              erewrite rqsQ_deqMP_rs by eassumption.
              reflexivity.
            }
            { solve_q. }
        + (** [RsUpDown] *)
          pose proof H2.
          eapply parentIdxOf_Some in H6; [|eassumption].
          destruct H6 as [rqUp [rsUp [down ?]]]; dest.
          assert (Some oidx <> Some (obj_idx obj)).
          { intro Hx; inv Hx; apply parentIdxOf_not_eq in H2; auto. }
          rewrite H19.
          destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
          * dest; split; [assumption|].
            eapply downLockedInv_orqs_preserved_downRq_rsbTo_2; try eassumption.
            { eapply downLockedInv_msgs_preserved; [eassumption|].
              intros; split.
              { rewrite rqsQ_enqMP_rs by assumption; solve_q. }
              { solve_q. }
            }
            { solve_midx_neq. }
            { mred. }
          * eapply downLockFreeInv_orqs_preserved_downRq_rsbTo_2; try eassumption.
            { eapply downLockFreeInv_msgs_preserved; [eassumption|].
              intros; split.
              { rewrite rqsQ_enqMP_rs by assumption; solve_q. }
              { solve_q. }
            }
            { mred. }
        + (** [RsUpUp] *)
          destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
          * dest; split; [assumption|].
            pose proof (H9 _ H2).
            destruct H11 as [odown [orsUp ?]]; dest.
            repeat disc_rule_minds.
            red in H9; red; intros.
            specialize (H9 _ H11).
            destruct H9 as [down [rsUp ?]]; dest.
            exists down, rsUp; repeat split; try assumption.
            destruct (eq_nat_dec cidx (obj_idx obj)); subst.
            { repeat disc_rule_minds.
              clear H13; find_if_inside.
              { red in H15; red; dest.
                xor3_inv3 H11;
                  [dest|red; mred; simpl; eexists; repeat split; assumption].
                replace (length
                           (rqsQ (enqMP (rqi_midx_rsb rqi)
                                        rsm (deqMsgs (idsOf mins) msgs)) odown)) with 0;
                  [|rewrite H19; solve_q; unfold rqsQ in H1, H11; omega].
                replace (length
                           (findQ (rqi_midx_rsb rqi)
                                  (enqMP (rqi_midx_rsb rqi)
                                         rsm (deqMsgs (idsOf mins) msgs)))) with 1;
                  [|rewrite H19; solve_q; rewrite app_length; simpl; omega].
                repeat split; try omega.
                xsnd; [omega|omega|].
                intro Hx; red in Hx; mred; simpl in Hx.
                destruct Hx as [xrqi [? ?]]; mred.
              }
              { exfalso; red in H15; dest.
                red in H11; mred.
              }
            }
            { rewrite H19.
              assert (Some oidx <> Some (obj_idx obj)).
              { intro Hx; inv Hx; apply parentIdxOf_not_eq in H2; auto. }
              clear H13; find_if_inside.
              { eapply downLockedChildInv_orqs_preserved_not_child_update; eauto.
                eapply downLockedChildInv_msgs_preserved; eauto; solve_q.
              }
              { eapply downLockFreeChildInv_orqs_preserved_not_child_update; eauto.
                eapply downLockFreeChildInv_msgs_preserved; eauto; solve_q.
              }
            }
          * exfalso; specialize (H _ H2).
            destruct H as [odown [orsUp ?]]; dest.
            repeat disc_rule_minds.
            red in H11; dest.
            red in H11; mred.

      - (** case [RsDownRqDownRule] *)
        disc_rule_conds.
        pose proof H2.
        eapply parentIdxOf_Some in H5; [|eassumption].
        destruct H5 as [rqUp [rsUp [down ?]]]; dest.
        repeat disc_rule_minds.
        assert (Some oidx <> Some (obj_idx obj)).
        { intro Hx; inv Hx; apply parentIdxOf_not_eq in H2; auto. }
        destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
        + dest; split; [assumption|].
          eapply downLockedInv_orqs_preserved_downRq_rsbTo_1; try eassumption.
          * eapply downLockedInv_msgs_preserved; [eassumption|].
            intros; split.
            { solve_q.
              eapply rqsQ_deqMP_rs in H8; [|eassumption]; eauto.
            }
            { solve_q. }
          * mred.
          * rewrite H27; solve_midx_neq.
        + eapply downLockFreeInv_orqs_preserved_downRq_rsbTo_1; try eassumption.
          * eapply downLockFreeInv_msgs_preserved; [eassumption|].
            intros; split.
            { solve_q.
              eapply rqsQ_deqMP_rs in H8; [|eassumption]; eauto.
            }
            { solve_q. }
          * mred.
          * rewrite H27; solve_midx_neq.
    Qed.

    Lemma downLockInvORq_step_int_other:
      forall oidx,
        DownLockInvORq orqs msgs oidx ((orqs@[oidx]) >>=[[]] (fun orq => orq)) ->
        In oidx (map (@obj_idx _) (sys_objs sys)) ->
        GoodRqRsRule dtr sys (obj_idx obj) rule ->
        oidx <> obj_idx obj ->
        parentIdxOf dtr (obj_idx obj) <> Some oidx ->
        DownLockInvORq (orqs+[obj_idx obj <- norq])
                       (enqMsgs mouts (deqMsgs (idsOf mins) msgs)) oidx
                       ((orqs@[ oidx]) >>=[[]] (fun orq => orq)).
    Proof.
      intros.
      destruct Hsd as [? [? _]].
      red in H; red.
      good_rqrs_rule_cases rule.

      - (** case [ImmDownRule] *)
        disc_rule_conds.
        destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
        + dest; split; [assumption|].
          eapply downLockedInv_orqs_preserved_not_child_update; [|eassumption].
          eapply downLockedInv_msgs_preserved; [eassumption|].
          intros; split.
          * rewrite rqsQ_enqMP_rs by assumption; solve_q.
          * solve_q.
        + eapply downLockFreeInv_orqs_preserved_not_child_update; [|eassumption].
          eapply downLockFreeInv_msgs_preserved; [eassumption|].
          intros; split.
          * rewrite rqsQ_enqMP_rs by assumption; solve_q.
          * solve_q.

      - (** case [ImmUpRule] *)
        disc_rule_conds.
        destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
        + dest; split; [assumption|].
          eapply downLockedInv_orqs_preserved_not_child_update; [|eassumption].
          eapply downLockedInv_msgs_preserved; [eassumption|].
          intros; destruct (eq_nat_dec cidx (obj_idx obj));
            subst; [elim H3; assumption|].
          split.
          * rewrite rqsQ_enqMP_rs by assumption; solve_q.
          * solve_q.
        + eapply downLockFreeInv_orqs_preserved_not_child_update; [|eassumption].
          eapply downLockFreeInv_msgs_preserved; [eassumption|].
          intros; destruct (eq_nat_dec cidx (obj_idx obj));
            subst; [elim H3; assumption|].
          split.
          * rewrite rqsQ_enqMP_rs by assumption; solve_q.
          * solve_q.

      - (** case [RqFwdRule] *)
        disc_rule_conds.
        + destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
          * dest; split; [assumption|].
            eapply downLockedInv_orqs_preserved_not_child_update; [|eassumption].
            eapply downLockedInv_msgs_preserved; [eassumption|].
            intros; split; solve_q.
          * eapply downLockFreeInv_orqs_preserved_not_child_update; [|eassumption].
            eapply downLockFreeInv_msgs_preserved; [eassumption|].
            intros; split; solve_q.
        + destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
          * dest; split; [assumption|].
            eapply downLockedInv_orqs_preserved_not_child_update; [|eassumption].
            eapply downLockedInv_msgs_preserved; [eassumption|].
            assert (Some oidx <> Some (obj_idx obj)) by congruence.
            intros; split; solve_q.
          * eapply downLockFreeInv_orqs_preserved_not_child_update; [|eassumption].
            eapply downLockFreeInv_msgs_preserved; [eassumption|].
            assert (Some oidx <> Some (obj_idx obj)) by congruence.
            intros; split; solve_q.
        + destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
          * dest; split; [assumption|].
            eapply downLockedInv_orqs_preserved_not_child_update; [|eassumption].
            eapply downLockedInv_msgs_preserved; [eassumption|].
            assert (Some oidx <> Some (obj_idx obj)) by congruence.
            intros; destruct (eq_nat_dec cidx (obj_idx obj));
              subst; [elim H3; assumption|].
            split; solve_q.
          * eapply downLockFreeInv_orqs_preserved_not_child_update; [|eassumption].
            eapply downLockFreeInv_msgs_preserved; [eassumption|].
            assert (Some oidx <> Some (obj_idx obj)) by congruence.
            intros; destruct (eq_nat_dec cidx (obj_idx obj));
              subst; [elim H3; assumption|].
            split; solve_q.

      - (** case [RsBackRule] *)
        good_footprint_get (obj_idx obj).
        disc_rule_conds.
        + destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
          * dest; split; [assumption|].
            eapply downLockedInv_orqs_preserved_not_child_update; [|eassumption].
            eapply downLockedInv_msgs_preserved; [eassumption|].
            intros; split.
            { rewrite rqsQ_enqMP_rs by assumption.
              erewrite rqsQ_deqMP_rs by eassumption.
              reflexivity.
            }
            { solve_q. }
          * eapply downLockFreeInv_orqs_preserved_not_child_update; [|eassumption].
            eapply downLockFreeInv_msgs_preserved; [eassumption|].
            intros; split.
            { rewrite rqsQ_enqMP_rs by assumption.
              erewrite rqsQ_deqMP_rs by eassumption.
              reflexivity.
            }
            { solve_q. }
        + destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
          * dest; split; [assumption|].
            eapply downLockedInv_orqs_preserved_not_child_update; [|eassumption].
            eapply downLockedInv_msgs_preserved; [eassumption|].
            assert (Some oidx <> Some (obj_idx obj)) by congruence.
            rewrite <-H20 in H13.
            intros; split; solve_q.
          * eapply downLockFreeInv_orqs_preserved_not_child_update; [|eassumption].
            eapply downLockFreeInv_msgs_preserved; [eassumption|].
            assert (Some oidx <> Some (obj_idx obj)) by congruence.
            rewrite <-H20 in H13.
            intros; split; solve_q.
        + destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
          * dest; split; [assumption|].
            eapply downLockedInv_orqs_preserved_not_child_update; [|eassumption].
            eapply downLockedInv_msgs_preserved; [eassumption|].
            assert (Some oidx <> Some (obj_idx obj)) by congruence.
            rewrite <-H20 in H8.
            intros; split.
            { solve_q. }
            { destruct (eq_nat_dec cidx (obj_idx obj)); subst; [elim H3; assumption|].
              solve_q.
            }
          * eapply downLockFreeInv_orqs_preserved_not_child_update; [|eassumption].
            eapply downLockFreeInv_msgs_preserved; [eassumption|].
            assert (Some oidx <> Some (obj_idx obj)) by congruence.
            rewrite <-H20 in H8.
            intros; split.
            { solve_q. }
            { destruct (eq_nat_dec cidx (obj_idx obj)); subst; [elim H3; assumption|].
              solve_q.
            }

      - (** case [RsDownRqDownRule] *)
        disc_rule_conds.
        destruct ((orqs@[oidx] >>=[[]] (fun orq => orq))@[downRq]).
        + dest; split; [assumption|].
          eapply downLockedInv_orqs_preserved_not_child_update; [|eassumption].
          eapply downLockedInv_msgs_preserved; [eassumption|].
          assert (Some oidx <> Some (obj_idx obj)) by congruence.
          intros; destruct (eq_nat_dec cidx (obj_idx obj));
            subst; [elim H3; assumption|].
          split; solve_q.
        + eapply downLockFreeInv_orqs_preserved_not_child_update; [|eassumption].
          eapply downLockFreeInv_msgs_preserved; [eassumption|].
          assert (Some oidx <> Some (obj_idx obj)) by congruence.
          intros; destruct (eq_nat_dec cidx (obj_idx obj));
            subst; [elim H3; assumption|].
          split; solve_q.
    Qed.

    Lemma downLockInv_step_int:
      DownLockInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      DownLockInv {| bst_oss := (oss) +[ obj_idx obj <- nost];
                     bst_orqs := (orqs) +[ obj_idx obj <- norq];
                     bst_msgs := enqMsgs mouts (deqMsgs (idsOf mins) msgs) |}.
    Proof.
      intros.
      do 2 red; simpl; intros.
      good_rqrs_rule_get rule.
      specialize (H _ H0); simpl in H; dest.

      M.cmp (obj_idx obj) oidx; mred; simpl in *.
      - (** case [oidx = obj_idx obj] *)
        apply downLockInvORq_step_int_me; assumption.
      - (** case [oidx <> obj_idx obj] *)
        remember (parentIdxOf dtr (obj_idx obj)) as opidx.
        destruct opidx as [pidx|].
        + destruct (eq_nat_dec oidx pidx); subst.
          * apply downLockInvORq_step_int_child; auto.
          * apply downLockInvORq_step_int_other; auto.
            rewrite <-Heqopidx.
            intro Hx; elim n0; inv Hx; reflexivity.
        + apply downLockInvORq_step_int_other; auto.
          rewrite <-Heqopidx; discriminate.
    Qed.

  End InternalStep.

  Lemma downLockInv_step:
    InvStep sys step_m DownLockInv.
  Proof.
    red; intros.
    inv H1.
    - auto.
    - apply downLockInv_step_ext_in; auto.
    - apply downLockInv_step_ext_out; auto.
      pose proof (extRssInv_ok Hers H).
      eapply msgs_ext_out_rss; eauto.
      apply H4.
    - eapply downLockInv_step_int; eauto.
      eapply footprints_ok; eassumption.
  Qed.

  Lemma downLockInv_ok:
    InvReachable sys step_m DownLockInv.
  Proof.
    apply inv_reachable.
    - apply downLockInv_init.
    - apply downLockInv_step.
  Qed.
  
End DownLockInv.

Lemma downLockInvORq_down_rqsQ_length_one_locked:
  forall dtr orqs msgs oidx orq cidx down,
    DownLockInvORq dtr orqs msgs oidx orq ->
    parentIdxOf dtr cidx = Some oidx ->
    edgeDownTo dtr cidx = Some down ->
    length (rqsQ msgs down) >= 1 ->
    exists rqid,
      orq@[downRq] = Some rqid /\
      DownLockedInv dtr orqs msgs oidx rqid /\
      exists rsUp,
        rsEdgeUpFrom dtr cidx = Some rsUp /\
        In rsUp rqid.(rqi_minds_rss).
Proof.
  intros.
  red in H; destruct (orq@[downRq]).
  - dest; exists r; repeat ssplit; auto.
    specialize (H3 _ H0).
    destruct H3 as [rdown [rsUp ?]]; dest.
    repeat disc_rule_minds.
    destruct (in_dec _ _ _); eauto.
    red in H5; dest.
    rewrite H1 in H2; simpl in H2; omega.
  - specialize (H _ H0); dest.
    repeat disc_rule_minds.
    red in H4; dest.
    rewrite H1 in H2; simpl in H2; omega.
Qed.

Lemma downLockInvORq_rsUp_length_one_locked:
  forall dtr orqs msgs oidx orq cidx rsUp,
    DownLockInvORq dtr orqs msgs oidx orq ->
    parentIdxOf dtr cidx = Some oidx ->
    rsEdgeUpFrom dtr cidx = Some rsUp ->
    length (findQ rsUp msgs) >= 1 ->
    exists rqid,
      orq@[downRq] = Some rqid /\
      DownLockedInv dtr orqs msgs oidx rqid /\
      In rsUp rqid.(rqi_minds_rss).
Proof.
  intros.
  red in H; destruct (orq@[downRq]).
  - dest; exists r; repeat ssplit; auto.
    specialize (H3 _ H0).
    destruct H3 as [down [rrsUp ?]]; dest.
    repeat disc_rule_minds.
    destruct (in_dec _ _ _); eauto.
    red in H5; dest.
    rewrite H5 in H2; simpl in H2; omega.
  - specialize (H _ H0); dest.
    repeat disc_rule_minds.
    red in H4; dest.
    rewrite H4 in H2; simpl in H2; omega.
Qed.

Lemma downLockInvORq_down_rqsQ_rsUp_False:
  forall dtr orqs msgs oidx orq cidx down rsUp,
    DownLockInvORq dtr orqs msgs oidx orq ->
    parentIdxOf dtr cidx = Some oidx ->
    edgeDownTo dtr cidx = Some down ->
    rsEdgeUpFrom dtr cidx = Some rsUp ->
    length (rqsQ msgs down) >= 1 ->
    length (findQ rsUp msgs) >= 1 ->
    False.
Proof.
  intros.
  red in H; destruct (orq@[downRq]).
  - dest; specialize (H5 _ H0).
    destruct H5 as [rdown [rrsUp ?]]; dest.
    repeat disc_rule_minds.
    destruct (in_dec _ _ _).
    + red in H7; dest.
      xor3_contra1 H7; omega.
    + red in H7; dest.
      rewrite H1 in H3; simpl in H3; omega.
  - specialize (H _ H0); dest.
    repeat disc_rule_minds.
    red in H6; dest.
    rewrite H1 in H3; simpl in H3; omega.
Qed.

Lemma downLockInvORq_down_rqsQ_length_two_False:
  forall dtr orqs msgs oidx orq cidx down,
    DownLockInvORq dtr orqs msgs oidx orq ->
    parentIdxOf dtr cidx = Some oidx ->
    edgeDownTo dtr cidx = Some down ->
    length (rqsQ msgs down) >= 2 ->
    False.
Proof.
  intros.
  red in H; destruct (orq@[downRq]).
  - dest; specialize (H3 _ H0).
    destruct H3 as [rdown [rsUp ?]]; dest.
    repeat disc_rule_minds.
    destruct (in_dec _ _ _).
    + red in H5; dest; omega.
    + red in H5; dest.
      destruct (rqsQ msgs down); simpl in *; [omega|discriminate].
  - specialize (H _ H0); dest.
    repeat disc_rule_minds.
    red in H4; dest.
    destruct (rqsQ msgs down); simpl in *; [omega|discriminate].
Qed.
    
Lemma downLockInvORq_rsUp_length_two_False:
  forall dtr orqs msgs oidx orq cidx rsUp,
    DownLockInvORq dtr orqs msgs oidx orq ->
    parentIdxOf dtr cidx = Some oidx ->
    rsEdgeUpFrom dtr cidx = Some rsUp ->
    length (findQ rsUp msgs) >= 2 ->
    False.
Proof.
  intros.
  red in H; destruct (orq@[downRq]).
  - dest; specialize (H3 _ H0).
    destruct H3 as [down [rrsUp ?]]; dest.
    repeat disc_rule_minds.
    destruct (in_dec _ _ _).
    + red in H5; dest; omega.
    + red in H5; dest.
      destruct (findQ rsUp msgs); simpl in *; [omega|discriminate].
  - specialize (H _ H0); dest.
    repeat disc_rule_minds.
    red in H4; dest.
    destruct (findQ rsUp msgs); simpl in *; [omega|discriminate].
Qed.

Close Scope list.
Close Scope fmap.

