Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsInvMsg RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Msi Ex.Msi.Msi Ex.Msi.MsiTopo.

Require Import Ex.Msi.MsiInv Ex.Msi.MsiInvB.
Require Export Ex.Msi.MsiInvInv0 Ex.Msi.MsiInvInv1.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Msi.ImplOStateIfc.

Definition NoCohMsgs (oidx: IdxT) (msgs: MessagePool Msg) :=
  MsgsNotExist [(downTo oidx, (MRs, msiRsS));
               (downTo oidx, (MRs, msiRsM));
               (rsUpFrom oidx, (MRs, msiDownRsS));
               (rsUpFrom oidx, (MRs, msiDownRsIM))] msgs.

Definition ObjInvalid0 (oidx: IdxT) (ost: OState) (msgs: MessagePool Msg) :=
  ost#[status] <= msiI /\
  ost#[dir].(dir_st) <> msiS /\
  NoCohMsgs oidx msgs.

Definition ObjInvalid (oidx: IdxT) (ost: OState) (msgs: MessagePool Msg) :=
  ObjInvalid0 oidx ost msgs \/ ObjInvRs oidx msgs.

Definition ObjsInvalid (inP: IdxT -> Prop) (oss: OStates) (msgs: MessagePool Msg) :=
  forall oidx,
    inP oidx ->
    ost <+- oss@[oidx]; ObjInvalid oidx ost msgs.

Definition InvObjExcl0 (eidx: IdxT) (ost: OState) (oss: OStates)
           (msgs: MessagePool Msg) :=
  ObjExcl0 eidx ost msgs ->
  ObjsInvalid (fun oidx => eidx <> oidx) oss msgs /\
  NoCohMsgs eidx msgs.

Definition ObjOwned (oidx: IdxT) (ost: OState) (msgs: MessagePool Msg) :=
  ost#[owned] = true /\ NoRsI oidx msgs.

Definition InvObjOwned (topo: DTree) (eidx: IdxT) (eost: OState) (oss: OStates)
           (msgs: MessagePool Msg) :=
  ObjOwned eidx eost msgs ->
  ObjsInvalid (fun oidx => ~ In oidx (subtreeIndsOf topo eidx)) oss msgs /\
  NoCohMsgs eidx msgs.

Definition InvDirInv (topo: DTree) (cifc: CIfc) (eidx: IdxT) (eost: OState) (oss: OStates)
           (msgs: MessagePool Msg) :=
  In eidx (c_li_indices cifc) ->
  forall cidx,
    parentIdxOf topo cidx = Some eidx ->
    (getDir cidx eost#[dir] = msiI ->
     ObjsInvalid (fun oidx => In oidx (subtreeIndsOf topo cidx)) oss msgs) /\
    (msiM <= getDir cidx eost#[dir] ->
     ObjsInvalid (fun oidx => ~ In oidx (subtreeIndsOf topo cidx)) oss msgs).

Definition InvExcl (topo: DTree) (cifc: CIfc) (st: State): Prop :=
  forall eidx,
    eost <+- (st_oss st)@[eidx];
      (InvObjExcl0 eidx eost (st_oss st) (st_msgs st) /\
       InvObjOwned topo eidx eost (st_oss st) (st_msgs st) /\
       InvDirInv topo cifc eidx eost (st_oss st) (st_msgs st)).

Section Facts.

  (** [ObjExcl0] *)

  Lemma ObjExcl0_enqMP_inv:
    forall oidx ost msgs midx msg,
      ObjExcl0 oidx ost (enqMP midx msg msgs) ->
      ObjExcl0 oidx ost msgs.
  Proof.
    unfold ObjExcl0; intros.
    dest; split; [assumption|].
    disc_MsgsP H0; assumption.
  Qed.

  Lemma ObjExcl0_enqMsgs_inv:
    forall oidx ost msgs nmsgs,
      ObjExcl0 oidx ost (enqMsgs nmsgs msgs) ->
      ObjExcl0 oidx ost msgs.
  Proof.
    unfold ObjExcl0; intros.
    dest; split; [assumption|].
    disc_MsgsP H0; assumption.
  Qed.

  Lemma ObjExcl0_other_midx_deqMP_inv:
    forall oidx ost msgs midx,
      ObjExcl0 oidx ost (deqMP midx msgs) ->
      midx <> downTo oidx ->
      ObjExcl0 oidx ost msgs.
  Proof.
    unfold ObjExcl0; intros.
    dest; split; [assumption|].
    disc_MsgsP H1; assumption.
  Qed.

  Lemma ObjExcl0_other_midx_deqMsgs_inv:
    forall oidx ost msgs (rmsgs: list (Id Msg)),
      ObjExcl0 oidx ost (deqMsgs (idsOf rmsgs) msgs) ->
      NoDup (idsOf rmsgs) ->
      Forall (FirstMPI msgs) rmsgs ->
      Forall (fun midx => midx <> downTo oidx) (idsOf rmsgs) ->
      ObjExcl0 oidx ost msgs.
  Proof.
    unfold ObjExcl0; intros.
    dest; split; [assumption|].
    apply MsgsP_other_midx_deqMsgs_inv in H3.
    - assumption.
    - simpl.
      simpl; apply (DisjList_spec_1 idx_dec); intros.
      rewrite Forall_forall in H2; specialize (H2 _ H4).
      intro Hx; dest_in; auto.
  Qed.

  Lemma ObjExcl0_other_msg_id_deqMP_inv:
    forall oidx ost msgs midx,
      ObjExcl0 oidx ost (deqMP midx msgs) ->
      forall msg,
        FirstMP msgs midx msg ->
        msg.(msg_id) <> msiInvRs ->
        ObjExcl0 oidx ost msgs.
  Proof.
    unfold ObjExcl0; intros.
    dest; split; [assumption|].
    eapply MsgsP_other_msg_id_deqMP_inv in H2;
      [|eassumption|simpl; intuition].
    assumption.
  Qed.

  Lemma ObjExcl0_other_msg_id_deqMsgs_inv:
    forall oidx ost msgs rmsgs,
      ObjExcl0 oidx ost (deqMsgs (idsOf rmsgs) msgs) ->
      NoDup (idsOf rmsgs) ->
      Forall (FirstMPI msgs) rmsgs ->
      Forall (fun idm => (valOf idm).(msg_id) <> msiInvRs) rmsgs ->
      ObjExcl0 oidx ost msgs.
  Proof.
    unfold ObjExcl0; intros.
    dest; split; [assumption|].
    eapply MsgsP_other_msg_id_deqMsgs_inv in H3; try assumption.
    simpl; apply (DisjList_spec_1 idx_dec); intros.
    apply in_map_iff in H4; dest; subst.
    rewrite Forall_forall in H2; specialize (H2 _ H5).
    intro Hx; dest_in; auto.
  Qed.

  (** [ObjInvalid] and [ObjsInvalid] *)

  Lemma ObjsInvalid_ObjInvalid:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall oidx ost,
        inP oidx ->
        oss@[oidx] = Some ost ->
        ObjInvalid oidx ost msgs.
  Proof.
    intros.
    specialize (H _ H0).
    rewrite H1 in H; simpl in H; assumption.
  Qed.

  Lemma ObjInvalid_NoCohMsgs:
    forall oidx ost orq msgs,
      RsDownConflicts oidx orq msgs ->
      ObjInvalid oidx ost msgs ->
      NoCohMsgs oidx msgs.
  Proof.
    intros.
    destruct H0; [apply H0|].
    destruct H0 as [[midx msg] [? ?]]; inv H1.
    red; intros.
    specialize (H (downTo oidx, msg) eq_refl H4 H0); dest.
    apply not_MsgExistsSig_MsgsNotExist; intros.
    dest_in.
    - destruct H9 as [[rmidx rmsg] [? ?]]; inv H9.
      eapply H2 with (rrsDown:= (downTo oidx, rmsg)); eauto.
      simpl; intro; subst.
      rewrite H5 in H13; discriminate.
    - destruct H9 as [[rmidx rmsg] [? ?]]; inv H9.
      eapply H2 with (rrsDown:= (downTo oidx, rmsg)); eauto.
      simpl; intro; subst.
      rewrite H5 in H13; discriminate.
    - destruct H9 as [[rmidx rmsg] [? ?]]; inv H9.
      eapply H7 with (rsUp:= (rsUpFrom oidx, rmsg)); eauto.
    - destruct H9 as [[rmidx rmsg] [? ?]]; inv H9.
      eapply H7 with (rsUp:= (rsUpFrom oidx, rmsg)); eauto.
  Qed.

  Lemma ObjsInvalid_impl:
    forall inP1 oss msgs,
      ObjsInvalid inP1 oss msgs ->
      forall (inP2: IdxT -> Prop),
        (forall oidx, inP2 oidx -> inP1 oidx) ->
        ObjsInvalid inP2 oss msgs.
  Proof.
    unfold ObjsInvalid; intros; auto.
  Qed.

  Lemma ObjsInvalid_obj_status_false:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall oidx,
        inP oidx ->
        NoRsI oidx msgs ->
        forall ost,
          oss@[oidx] = Some ost ->
          msiS <= ost#[status] ->
          False.
  Proof.
    intros.
    specialize (H _ H0).
    rewrite H2 in H; simpl in H.
    destruct H.
    - red in H; solve_msi.
    - eapply NoRsI_MsgExistsSig_InvRs_false; eauto.
  Qed.

  Lemma ObjsInvalid_obj_dir_false:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall oidx,
        inP oidx ->
        NoRsI oidx msgs ->
        forall ost,
          oss@[oidx] = Some ost ->
          ost#[dir].(dir_st) = msiS ->
          False.
  Proof.
    intros.
    specialize (H _ H0).
    rewrite H2 in H; simpl in H.
    destruct H.
    - red in H; solve_msi.
    - eapply NoRsI_MsgExistsSig_InvRs_false; eauto.
  Qed.

  Lemma ObjsInvalid_this_state_silent:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall roidx nost,
        ~ inP roidx ->
        ObjsInvalid inP (oss +[roidx <- nost]) msgs.
  Proof.
    intros.
    red; intros.
    specialize (H _ H1).
    mred.
  Qed.

  Lemma ObjsInvalid_this_enqMP_silent:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall roidx,
        ~ inP roidx ->
        forall midx msg,
          In midx [rqUpFrom roidx; rsUpFrom roidx; downTo roidx] ->
          ObjsInvalid inP oss (enqMP midx msg msgs).
  Proof.
    intros.
    red; intros.
    specialize (H _ H2).
    destruct (oss@[oidx]) as [ost|]; simpl in H; simpl; auto.
    destruct H.
    - left.
      destruct H as [? [? ?]].
      repeat split; [assumption..|dest_in; solve_MsgsP].
    - right.
      destruct H as [[rmidx rmsg] [? ?]]; inv H3.
      exists (downTo oidx, rmsg); split.
      + apply InMP_or_enqMP; right; assumption.
      + unfold sigOf; simpl; congruence.
  Qed.

  Lemma ObjsInvalid_this_deqMP_silent:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall roidx,
        ~ inP roidx ->
        forall midx,
          In midx [rqUpFrom roidx; rsUpFrom roidx; downTo roidx] ->
          ObjsInvalid inP oss (deqMP midx msgs).
  Proof.
    intros.
    red; intros.
    specialize (H _ H2).
    destruct (oss@[oidx]) as [ost|]; simpl in H; simpl; auto.
    destruct H.
    - left.
      destruct H as [? [? ?]].
      repeat split; [assumption..|dest_in; solve_MsgsP].
    - right.
      destruct H as [[rmidx msg] [? ?]]; inv H3.
      exists (downTo oidx, msg); split.
      + apply deqMP_InMP_midx; [assumption|].
        simpl; intro Hx; subst.
        dest_in; try discriminate.
        inv H3; auto.
      + unfold sigOf; simpl; congruence.
  Qed.

  Lemma ObjsInvalid_rsS_false:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall oidx ost orq,
        oss@[oidx] = Some ost ->
        inP oidx ->
        RsDownConflicts oidx orq msgs ->
        forall rsdm,
          InMP (downTo oidx) rsdm msgs ->
          rsdm.(msg_type) = MRs ->
          rsdm.(msg_id) = msiRsS ->
          False.
  Proof.
    intros.
    specialize (H _ H1).
    rewrite H0 in H; simpl in H.
    destruct H.
    - red in H; dest.
      specialize (H7 (downTo oidx, rsdm) H3).
      red in H7; rewrite map_trans, map_cons in H7.
      rewrite caseDec_head_eq in H7
        by (unfold sigOf; simpl; congruence).
      auto.
    - destruct H as [[midx msg] [? ?]]; simpl in *.
      unfold sigOf in H6; simpl in H6; inv H6.
      specialize (H2 (downTo oidx, rsdm) eq_refl H4 H3); dest.
      eapply (H7 (downTo oidx, msg)); eauto.
      simpl; intro Hx; subst.
      rewrite H5 in H10; discriminate.
  Qed.

  Lemma ObjsInvalid_rsM_false:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall oidx ost orq,
        oss@[oidx] = Some ost ->
        inP oidx ->
        RsDownConflicts oidx orq msgs ->
        forall rsdm,
          InMP (downTo oidx) rsdm msgs ->
          rsdm.(msg_type) = MRs ->
          rsdm.(msg_id) = msiRsM ->
          False.
  Proof.
    intros.
    specialize (H _ H1).
    rewrite H0 in H; simpl in H.
    destruct H.
    - red in H; dest.
      specialize (H7 (downTo oidx, rsdm) H3).
      red in H7; rewrite map_trans, map_cons in H7.
      rewrite caseDec_head_neq in H7
        by (unfold sigOf; simpl; intro Hx; inv Hx;
            rewrite H5 in H10; discriminate).
      rewrite map_cons in H7.
      rewrite caseDec_head_eq in H7
        by (unfold sigOf; simpl; congruence).
      auto.
    - destruct H as [[midx msg] [? ?]]; simpl in *.
      unfold sigOf in H6; simpl in H6; inv H6.
      specialize (H2 (downTo oidx, rsdm) eq_refl H4 H3); dest.
      eapply (H7 (downTo oidx, msg)); eauto.
      simpl; intro Hx; subst.
      rewrite H5 in H10; discriminate.
  Qed.

  Lemma ObjsInvalid_downRsS_false:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall oidx ost orq,
        oss@[oidx] = Some ost ->
        inP oidx ->
        RsDownConflicts oidx orq msgs ->
        forall rsum,
          InMP (rsUpFrom oidx) rsum msgs ->
          rsum.(msg_type) = MRs ->
          rsum.(msg_id) = msiDownRsS ->
          False.
  Proof.
    intros.
    specialize (H _ H1).
    rewrite H0 in H; simpl in H.
    destruct H.
    - red in H; dest.
      specialize (H7 (rsUpFrom oidx, rsum) H3).
      red in H7; rewrite map_trans, map_cons in H7.
      do 2 (rewrite caseDec_head_neq in H7
             by (unfold sigOf; simpl; intro Hx; inv Hx;
                 rewrite H5 in H10; discriminate);
            rewrite map_cons in H7).
      rewrite caseDec_head_eq in H7
        by (unfold sigOf; simpl; congruence).
      auto.
    - destruct H as [[midx msg] [? ?]]; simpl in *.
      unfold sigOf in H6; simpl in H6; inv H6.
      specialize (H2 (downTo oidx, msg) eq_refl H9 H); dest.
      eapply (H12 (rsUpFrom oidx, rsum)); eauto.
  Qed.

  Lemma ObjsInvalid_downRsIM_false:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall oidx ost orq,
        oss@[oidx] = Some ost ->
        inP oidx ->
        RsDownConflicts oidx orq msgs ->
        forall rsum,
          InMP (rsUpFrom oidx) rsum msgs ->
          rsum.(msg_type) = MRs ->
          rsum.(msg_id) = msiDownRsIM ->
          False.
  Proof.
    intros.
    specialize (H _ H1).
    rewrite H0 in H; simpl in H.
    destruct H.
    - red in H; dest.
      specialize (H7 (rsUpFrom oidx, rsum) H3).
      red in H7; rewrite map_trans, map_cons in H7.
      do 3 (rewrite caseDec_head_neq in H7
             by (unfold sigOf; simpl; intro Hx; inv Hx;
                 rewrite H5 in H10; discriminate);
            rewrite map_cons in H7).
      rewrite caseDec_head_eq in H7
        by (unfold sigOf; simpl; congruence).
      auto.
    - destruct H as [[midx msg] [? ?]]; simpl in *.
      unfold sigOf in H6; simpl in H6; inv H6.
      specialize (H2 (downTo oidx, msg) eq_refl H9 H); dest.
      eapply (H12 (rsUpFrom oidx, rsum)); eauto.
  Qed.

  Lemma NoCohMsgs_enq:
    forall msgs oidx,
      NoCohMsgs oidx msgs ->
      forall midx msg,
        ~ In msg.(msg_id) [msiRsS; msiRsM; msiDownRsS; msiDownRsIM] ->
        NoCohMsgs oidx (enqMP midx msg msgs).
  Proof.
    intros; apply MsgsP_other_msg_id_enqMP; assumption.
  Qed.

  Lemma NoCohMsgs_rqDown_deq:
    forall msgs oidx rmsg,
      FirstMPI msgs (downTo oidx, rmsg) ->
      rmsg.(msg_type) = MRq ->
      forall orq,
        RsDownConflicts oidx orq msgs ->
        RqDownConflicts oidx msgs ->
        NoCohMsgs oidx (deqMP (downTo oidx) msgs).
  Proof.
    intros.
    specialize (H2 (downTo oidx, rmsg) eq_refl H0 (FirstMP_InMP H)); dest.
    apply not_MsgExistsSig_MsgsNotExist.
    intros; dest_in.
    1-3: try (destruct H5 as [[rsDown rsdm] [? ?]]; inv H5;
              apply InMP_deqMP in H4;
              specialize (H1 (downTo oidx, rsdm) eq_refl H8 H4); dest;
              eapply H10 with (rqDown:= (downTo oidx, rmsg)); eauto).
    all: try (destruct H5 as [rsUp [? ?]]; inv H5;
              apply H3 with (rsUp:= rsUp); auto;
              eapply InMP_deqMP; eauto).
  Qed.

  Lemma NoCohMsgs_rsDown_deq:
    forall msgs oidx rmsg,
      FirstMPI msgs (downTo oidx, rmsg) ->
      rmsg.(msg_type) = MRs ->
      forall orq,
        RsDownConflicts oidx orq msgs ->
        NoCohMsgs oidx (deqMP (downTo oidx) msgs).
  Proof.
    intros.
    specialize (H1 (downTo oidx, rmsg) eq_refl H0 (FirstMP_InMP H)); dest.
    apply not_MsgExistsSig_MsgsNotExist.
    intros; dest_in.
    1-2: try (destruct H8 as [[midx msg] [? ?]]; inv H8;
              apply H4;
              eapply rssQ_deq_in_length_two; eauto).
    all: try (destruct H8 as [rsUp [? ?]]; inv H8;
              apply H6 with (rsUp:= rsUp); auto;
              eapply InMP_deqMP; eauto).
  Qed.

  Lemma NoCohMsgs_rsUp_in:
    forall oidx msgs rmsg,
      InMP (rsUpFrom oidx) rmsg msgs ->
      rmsg.(msg_id) <> msiDownRsS ->
      rmsg.(msg_id) <> msiDownRsIM ->
      forall orq,
        RsDownConflicts oidx orq msgs ->
        RsUpConflicts oidx msgs ->
        NoCohMsgs oidx msgs.
  Proof.
    intros.
    specialize (H3 (rsUpFrom oidx, rmsg) eq_refl H); dest.
    apply not_MsgExistsSig_MsgsNotExist.
    intros; dest_in.
    all: try (destruct H7 as [[midx msg] [? ?]]; inv H7;
              specialize (H2 (downTo oidx, msg) eq_refl H10 H6); dest;
              eapply H13 with (rsUp:= (rsUpFrom oidx, rmsg)); eauto; fail).
    all: (destruct H7 as [[midx msg] [? ?]]; inv H7;
          eapply H4;
          eapply findQ_length_two; [|apply H|apply H6];
          simpl; intro Hx; subst;
          congruence).
  Qed.

  Lemma NoCohMsgs_rsUp_deq:
    forall msgs oidx rmsg,
      FirstMPI msgs (rsUpFrom oidx, rmsg) ->
      forall orq,
        RsDownConflicts oidx orq msgs ->
        RsUpConflicts oidx msgs ->
        NoCohMsgs oidx (deqMP (rsUpFrom oidx) msgs).
  Proof.
    intros.
    specialize (H1 (rsUpFrom oidx, rmsg) eq_refl (FirstMP_InMP H)); dest.
    apply not_MsgExistsSig_MsgsNotExist.
    intros; dest_in.
    1-3: try (destruct H5 as [[midx msg] [? ?]]; inv H5;
              apply InMP_deqMP in H4;
              specialize (H0 (downTo oidx, msg) eq_refl H8 H4); dest;
              eapply H11 with (rsUp:= (rsUpFrom oidx, rmsg)); eauto;
              apply FirstMP_InMP; assumption).
    all: try (destruct H5 as [[midx msg] [? ?]]; inv H5;
              eapply H2;
              eapply findQ_deq_in_length_two; eauto).
  Qed.

  Lemma NoCohMsgs_deqMsgs_silent:
    forall rminds msgs oidx,
      NoCohMsgs oidx msgs ->
      NoCohMsgs oidx (deqMsgs rminds msgs).
  Proof.
    intros; solve_MsgsP.
  Qed.

  Lemma NoCohMsgs_rsUps_deq:
    forall rminds msgs oidx,
      Forall (fun midx => exists rcidx, midx = rsUpFrom rcidx) rminds ->
      NoDup rminds ->
      In (rsUpFrom oidx) rminds ->
      NoCohMsgs oidx (deqMP (rsUpFrom oidx) msgs) ->
      NoCohMsgs oidx (deqMsgs rminds msgs).
  Proof.
    induction rminds; simpl; intros; [exfalso; auto|].
    inv H; inv H0.
    destruct H5 as [rcidx ?]; subst.
    destruct H1.
    - apply NoCohMsgs_deqMsgs_silent.
      rewrite H; assumption.
    - rewrite <-deqMP_deqMsgs_comm by assumption.
      apply NoCohMsgs_deqMsgs_silent with (rminds:= [rsUpFrom rcidx]).
      eapply IHrminds; eauto.
  Qed.

  Lemma ObjsInvalid_invRs:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall oidx orq,
        inP oidx ->
        RsDownConflicts oidx orq msgs ->
        forall nost: OState,
          nost#[status] = msiNP ->
          nost#[dir].(dir_st) = msiI -> (* by [InvWBDir] *)
          nost#[owned] = false ->
          forall rmsg,
            FirstMPI msgs (downTo oidx, rmsg) ->
            rmsg.(msg_type) = MRs ->
            ObjsInvalid inP (oss +[ oidx <- nost]) (deqMP (downTo oidx) msgs).
  Proof.
    intros.
    red; intros roidx ?.
    specialize (H _ H7).
    mred; simpl in *; auto.
    - left; repeat split.
      + simpl; solve_msi.
      + simpl; rewrite H3; discriminate.
      + eapply NoCohMsgs_rsDown_deq; eauto.
    - destruct (oss@[roidx]) as [rost|]; simpl in *; auto.
      destruct H; [left|right].
      + destruct H as [? [? ?]]; repeat split; [assumption..|].
        solve_MsgsP.
      + destruct H as [[midx msg] [? ?]].
        exists (midx, msg); split; [|assumption]; inv H8.
        apply deqMP_InMP_midx; [assumption|].
        simpl; intro Hx; subst.
        inv Hx; auto.
  Qed.

  Section OnTree.
    Variable (tr: tree).
    Hypothesis (Htr: tr <> Node nil).

    Let topo: DTree := fst (tree2Topo tr 0).
    Let cifc: CIfc := snd (tree2Topo tr 0).

    Lemma ObjsInvalid_shrinked:
      forall eidx,
        In eidx (c_l1_indices cifc) ->
        forall oss msgs,
          ObjsInvalid (fun oidx => ~ In oidx (subtreeIndsOf topo eidx)) oss msgs ->
          (forall oidx, _ <+- oss@[oidx]; In oidx (c_li_indices cifc ++ c_l1_indices cifc)) ->
          ObjsInvalid (fun oidx => eidx <> oidx) oss msgs.
    Proof.
      intros.
      red; intros.
      destruct (oss@[oidx]) as [ost|] eqn:Host; simpl; [|auto].
      specialize (H1 oidx); rewrite Host in H1; simpl in H1.
      specialize (H0 oidx); simpl in H0.
      rewrite Host in H0; simpl in H0.
      apply H0.
      subst topo; rewrite tree2Topo_l1_subtreeIndsOf; [|eassumption].
      intro Hx; dest_in; [auto|].
      eapply tree2Topo_l1_child_ext_not_in; eauto.
    Qed.

    Lemma ObjsInvalid_child_forall:
      forall oidx oss msgs,
        (forall cidx,
            parentIdxOf topo cidx = Some oidx ->
            ObjsInvalid (fun idx => In idx (subtreeIndsOf topo cidx)) oss msgs) ->
        ObjsInvalid
          (fun idx =>
             exists cidx,
               parentIdxOf topo cidx = Some oidx /\
               In idx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx))
          oss msgs.
    Proof.
      intros.
      red; intros.
      destruct H0 as [cidx [? ?]].
      specialize (H _ H0 _ H1).
      assumption.
    Qed.

    Lemma ObjsInvalid_l1_singleton:
      forall oss orqs msgs,
        InObjInds tr 0 {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
        forall eidx,
          In eidx (c_l1_indices cifc) ->
          ObjsInvalid
            (fun oidx =>
               exists ecidx,
                 parentIdxOf topo ecidx = Some eidx /\
                 In oidx (subtreeIndsOf topo ecidx)) oss msgs.
    Proof.
      intros; subst topo.
      red; intros.
      destruct (oss@[oidx]) as [ost|] eqn:Host; simpl; [|auto].
      assert (oidx <> eidx /\
              In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) eidx)).
      { destruct H1 as [ecidx [? ?]].
        split.
        { intro; subst.
          eapply parent_not_in_subtree; eauto.
        }
        { eapply subtreeIndsOf_child_SubList; eauto. }
      }
      clear H1; dest.

      rewrite tree2Topo_l1_subtreeIndsOf in H2 by assumption.
      dest_in; [exfalso; auto|].
      exfalso.
      specialize (H (l1ExtOf eidx)); simpl in H.
      rewrite Host in H; simpl in H.
      eapply tree2Topo_l1_child_ext_not_in; eauto.
    Qed.

    Lemma ObjsInvalid_this_rsUps_deqMsgs_silent:
      forall inP oss msgs,
        ObjsInvalid inP oss msgs ->
        forall pidx,
          ~ inP pidx ->
          forall rminds,
            Forall (fun midx =>
                      exists cidx,
                        parentIdxOf topo cidx = Some pidx /\
                        midx = rsUpFrom cidx) rminds ->
            ObjsInvalid inP oss (deqMsgs rminds msgs).
    Proof.
      intros.
      red; intros.
      specialize (H _ H2).
      destruct (oss@[oidx]) as [ost|]; simpl in H; simpl; auto.
      destruct H.
      - left.
        destruct H as [? [? ?]].
        repeat split; [assumption..|dest_in; solve_MsgsP].
      - right.
        destruct H as [[rmidx msg] [? ?]]; inv H3.
        exists (downTo oidx, msg); split.
        + apply deqMsgs_InMP_midx; [assumption|].
          simpl; intro Hx.
          rewrite Forall_forall in H1; specialize (H1 _ Hx).
          dest; discriminate.
        + unfold sigOf; simpl; congruence.
    Qed.

    Lemma ObjsInvalid_rsDown_invalidated:
      forall oss msgs oidx orq,
        ObjsInvalid (fun idx => oidx <> idx) oss msgs ->
        RsDownConflicts oidx orq msgs ->
        forall cidx (nost: OState) rmsg,
          parentIdxOf topo cidx = Some oidx ->
          nost#[status] <= msiI ->
          nost#[dir].(dir_st) <> msiS ->
          FirstMPI msgs (downTo oidx, rmsg) ->
          rmsg.(msg_type) = MRs ->
          ObjsInvalid (fun idx => cidx <> idx)
                      (oss +[oidx <- nost])
                      (deqMP (downTo oidx) msgs).
    Proof.
      intros; subst topo.
      red; intros; mred.
      - simpl; left; repeat split.
        + simpl in *; solve_msi.
        + assumption.
        + eapply NoCohMsgs_rsDown_deq; eauto.
      - specialize (H _ (neq_sym n)).
        destruct (oss@[oidx0]) as [ost|]; simpl in *; auto.
        destruct H; [left|right].
        + destruct H as [? [? ?]].
          repeat split; [assumption..|solve_MsgsP].
        + destruct H as [[midx msg] [? ?]].
          exists (midx, msg); split; [|assumption]; inv H7.
          apply deqMP_InMP_midx; [assumption|].
          simpl; intro Hx; subst.
          inv Hx; auto.
    Qed.

    Lemma ObjsInvalid_rsM_consumed:
      forall oss msgs oidx (ost: OState) orq,
        In oidx (c_li_indices cifc) ->
        ObjsInvalid (fun idx => ~ In idx (subtreeIndsOf topo oidx)) oss msgs ->
        RsDownConflicts oidx orq msgs ->
        ost#[dir].(dir_st) = msiI ->
        InvDirInv topo cifc oidx ost oss msgs ->
        forall cidx (nost: OState) rmsg,
          nost#[status] <= msiI ->
          nost#[dir].(dir_st) = msiM ->
          FirstMPI msgs (downTo oidx, rmsg) ->
          rmsg.(msg_type) = MRs ->
          ObjsInvalid (fun idx => ~ In idx (subtreeIndsOf topo cidx))
                      (oss +[oidx <- nost])
                      (deqMP (downTo oidx) msgs).
    Proof.
      intros; subst topo.
      red; intros; mred.
      - simpl; left; repeat split.
        + simpl in *; solve_msi.
        + rewrite H5; discriminate.
        + eapply NoCohMsgs_rsDown_deq; eauto.
      - destruct (in_dec idx_dec oidx0 (subtreeIndsOf (fst (tree2Topo tr 0)) oidx)).
        + apply subtreeIndsOf_composed in i; auto.
          destruct i; [exfalso; auto|].
          destruct H9 as [rcidx [? ?]].

          (* Discharge [InvDirInv] *)
          specialize (H3 H _ H9); destruct H3 as [? _].
          specialize (H3 (getDir_st_I _ H2 _)).
          specialize (H3 _ H10).

          destruct (oss@[oidx0]) as [ost0|]; simpl in *; auto.
          destruct H3; [left|right].
          * destruct H3 as [? [? ?]].
            repeat split; [assumption..|solve_MsgsP].
          * destruct H3 as [[midx msg] [? ?]].
            exists (midx, msg); split; [|assumption]; inv H11.
            apply deqMP_InMP_midx; [assumption|].
            simpl; intro Hx; subst.
            inv Hx; auto.

        + specialize (H0 _ n0).
          destruct (oss@[oidx0]) as [ost0|]; simpl in *; auto.
          destruct H0; [left|right].
          * destruct H0 as [? [? ?]].
            repeat split; [assumption..|solve_MsgsP].
          * destruct H0 as [[midx msg] [? ?]].
            exists (midx, msg); split; [|assumption]; inv H9.
            apply deqMP_InMP_midx; [assumption|].
            simpl; intro Hx; subst.
            inv Hx; auto.
    Qed.

    Lemma ObjsInvalid_rsM_generated:
      forall oss msgs oidx,
        ObjsInvalid (fun idx => oidx <> idx) oss msgs ->
        NoCohMsgs oidx msgs ->
        forall cidx (nost: OState),
          parentIdxOf topo cidx = Some oidx ->
          nost#[status] <= msiI ->
          nost#[dir].(dir_st) <> msiS ->
          ObjsInvalid (fun idx => ~ In idx (subtreeIndsOf topo cidx))
                      (oss +[oidx <- nost])
                      msgs.
    Proof.
      intros; subst topo.
      red; intros; mred; auto.
      simpl; left; repeat split.
      - simpl in *; solve_msi.
      - assumption.
      - assumption.
    Qed.

    Lemma ObjsInvalid_downRsIS:
      forall oss msgs oidx (ost: OState) orq,
        In oidx (c_li_indices cifc) ->
        RqDownConflicts oidx msgs ->
        RsDownConflicts oidx orq msgs ->
        ost#[dir].(dir_st) = msiI ->
        InvDirInv topo cifc oidx ost oss msgs ->
        forall (nost: OState) rqm rsm,
          nost#[status] <= msiI ->
          nost#[dir].(dir_st) = msiI ->
          FirstMPI msgs (downTo oidx, rqm) ->
          rqm.(msg_type) = MRq ->
          rsm.(msg_id) = msiDownRsIS ->
          ObjsInvalid
            (fun idx => In idx (subtreeIndsOf topo oidx))
            (oss +[oidx <- nost])
            (enqMP (rsUpFrom oidx) rsm (deqMP (downTo oidx) msgs)).
    Proof.
      intros; subst topo.
      red; intros; mred.
      - simpl; left; repeat split; [solve_msi| |].
        + rewrite H5; discriminate.
        + apply NoCohMsgs_enq; [|rewrite H8; solve_not_in].
          eapply NoCohMsgs_rqDown_deq; eauto.
      - apply subtreeIndsOf_composed in H9; auto.
        destruct H9; [exfalso; auto|].
        destruct H9 as [cidx [? ?]].
        destruct (oss@[oidx0]) as [ost0|] eqn:Host; simpl; auto.

        (* Discharge [InvDirInv] *)
        specialize (H3 H _ H9); destruct H3 as [? _].
        specialize (H3 (getDir_st_I _ H2 _)).
        specialize (H3 _ H10).

        rewrite Host in H3; simpl in H3.
        destruct H3; [left|right].
        + destruct H3 as [? [? ?]]; repeat split; [assumption..|].
          solve_MsgsP.
        + destruct H3 as [[midx msg] [? ?]].
          exists (midx, msg); split; [|assumption]; inv H11.
          apply InMP_or_enqMP; right.
          apply deqMP_InMP_midx; [assumption|].
          simpl; intro Hx; inv Hx; auto.
    Qed.

    Lemma ObjsInvalid_downRsIM:
      forall oss msgs oidx (ost: OState) orq,
        In oidx (c_li_indices cifc) ->
        RqDownConflicts oidx msgs ->
        RsDownConflicts oidx orq msgs ->
        ost#[dir].(dir_st) = msiI ->
        InvDirInv topo cifc oidx ost oss msgs ->
        forall (nost: OState) rqm rsm,
          nost#[status] <= msiI ->
          FirstMPI msgs (downTo oidx, rqm) ->
          rqm.(msg_type) = MRq ->
          rsm.(msg_id) = msiDownRsIM ->
          ObjsInvalid
            (fun idx =>
               exists cidx,
                 parentIdxOf topo cidx = Some oidx /\
                 In idx (subtreeIndsOf topo cidx))
            (oss +[oidx <- nost])
            (enqMP (rsUpFrom oidx) rsm (deqMP (downTo oidx) msgs)).
    Proof.
      intros; subst topo.
      red; intros; mred.
      - exfalso.
        destruct H8 as [cidx [? ?]].
        eapply parent_not_in_subtree; eauto.
      - destruct H8 as [cidx [? ?]].
        destruct (oss@[oidx0]) as [ost0|] eqn:Host; simpl; auto.

        (* Discharge [InvDirInv] *)
        specialize (H3 H _ H8); destruct H3 as [? _].
        specialize (H3 (getDir_st_I _ H2 _)).
        specialize (H3 _ H9).

        rewrite Host in H3; simpl in H3.
        destruct H3; [left|right].
        + destruct H3 as [? [? ?]]; repeat split; [assumption..|].
          solve_MsgsP.
        + destruct H3 as [[midx msg] [? ?]].
          exists (midx, msg); split; [|assumption]; inv H10.
          apply InMP_or_enqMP; right.
          apply deqMP_InMP_midx; [assumption|].
          simpl; intro Hx; inv Hx; auto.
    Qed.

    Lemma ObjsInvalid_out_composed:
      forall oidx oss msgs,
        ObjsInvalid
          (fun idx => ~ In idx (subtreeIndsOf topo oidx))
          oss msgs ->
        forall ost,
          oss@[oidx] = Some ost ->
          ObjInvalid oidx ost msgs ->
          forall cidx,
            parentIdxOf topo cidx = Some oidx ->
            (forall rcidx,
                rcidx <> cidx ->
                parentIdxOf topo rcidx = Some oidx ->
                ObjsInvalid
                  (fun idx => In idx (subtreeIndsOf topo rcidx))
                  oss msgs) ->
            ObjsInvalid
              (fun idx => ~ In idx (subtreeIndsOf topo cidx))
              oss msgs.
    Proof.
      intros.
      red; intros toidx ?.
      destruct (oss@[toidx]) as [tost|] eqn:Htost; simpl; auto.
      destruct (in_dec idx_dec toidx (subtreeIndsOf topo oidx)).
      - apply subtreeIndsOf_composed in i;
          [|apply tree2Topo_WfDTree].
        destruct i as [|[tcidx [? ?]]]; subst.
        + congruence.
        + destruct (idx_dec tcidx cidx); [subst; exfalso; auto|].
          specialize (H3 _ n H5 _ H6).
          rewrite Htost in H3; simpl in H3; assumption.
      - specialize (H _ n).
        rewrite Htost in H; simpl in H; assumption.
    Qed.

    Lemma ObjsInvalid_in_composed:
      forall oidx oss msgs ost,
        oss@[oidx] = Some ost ->
        ObjInvalid oidx ost msgs ->
        ObjsInvalid
          (fun idx =>
             exists rcidx,
               parentIdxOf topo rcidx = Some oidx /\
               In idx (subtreeIndsOf topo rcidx)) oss msgs ->
        ObjsInvalid
          (fun idx => In idx (subtreeIndsOf topo oidx))
          oss msgs.
    Proof.
      intros.
      red; intros toidx ?.
      destruct (oss@[toidx]) as [tost|] eqn:Htost; simpl; auto.
      apply subtreeIndsOf_composed in H2;
        [|apply tree2Topo_WfDTree].
      destruct H2 as [|[tcidx [? ?]]]; subst.
      - congruence.
      - specialize (H1 toidx); simpl in H1.
        rewrite Htost in H1; simpl in H1.
        apply H1; eauto.
    Qed.

    Lemma ObjsInvalid_downRsIM_composed:
      forall oidx oss msgs ost,
        oss@[oidx] = Some ost ->
        (forall rcidx,
            parentIdxOf topo rcidx = Some oidx ->
            ObjsInvalid
              (fun idx => In idx (subtreeIndsOf topo rcidx))
              oss msgs) ->
        ObjsInvalid
          (fun idx =>
             exists cidx,
               parentIdxOf topo cidx = Some oidx /\
               In idx (subtreeIndsOf topo cidx)) oss msgs.
    Proof.
      intros.
      red; intros toidx ?.
      destruct (oss@[toidx]) as [tost|] eqn:Htost; simpl; auto.
      destruct H1 as [cidx [? ?]].
      specialize (H0 _ H1 _ H2).
      rewrite Htost in H0; simpl in H0.
      assumption.
    Qed.

    Lemma ObjsInvalid_invRs_composed:
      forall oidx oss msgs,
        ObjsInvalid (fun idx => ~ In idx (subtreeIndsOf topo oidx)) oss msgs ->
        ObjsInvalid
          (fun idx =>
             exists rcidx,
               parentIdxOf topo rcidx = Some oidx /\
               In idx (subtreeIndsOf topo rcidx)) oss msgs ->
        ObjsInvalid (fun idx => oidx <> idx) oss msgs.
    Proof.
      intros.
      red; intros toidx ?.
      destruct (oss@[toidx]) as [tost|] eqn:Htost; simpl; auto.
      destruct (in_dec idx_dec toidx (subtreeIndsOf topo oidx)).
      - apply subtreeIndsOf_composed in i; [|apply tree2Topo_WfDTree].
        destruct i as [|[tcidx [? ?]]]; subst.
        + congruence.
        + specialize (H0 toidx); simpl in H0.
          rewrite Htost in H0; simpl in H0.
          apply H0; eauto.
      - eapply ObjsInvalid_ObjInvalid; try exact H; auto.
    Qed.

  End OnTree.

End Facts.

Ltac disc_ObjExcl0_msgs H :=
  repeat
    (first [apply ObjExcl0_enqMP_inv in H
           |apply ObjExcl0_enqMsgs_inv in H
           |apply ObjExcl0_other_midx_deqMP_inv in H;
            [|solve_chn_neq; fail]
           |apply ObjExcl0_other_midx_deqMsgs_inv in H;
            [|eassumption|eassumption|]
           |eapply ObjExcl0_other_msg_id_deqMP_inv in H;
            [|eassumption
             |simpl; try match goal with
                         | [H: ?lh = _ |- ?lh <> _] => rewrite H
                         end; discriminate]
           |eapply ObjExcl0_other_msg_id_deqMsgs_inv in H;
            [|eassumption|eassumption|]
    ]).

Section InvExcl.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Local Notation topo := (fst (tree2Topo tr 0)).
  Local Notation cifc := (snd (tree2Topo tr 0)).
  Local Notation impl := (impl Htr).

  Lemma ObjInvalid_init:
    forall oidx, ObjInvalid oidx implOStateInit (emptyMP Msg).
  Proof.
    intros; left.
    repeat split; [simpl; solve_msi|simpl; solve_msi|].
    do 3 red; intros.
    do 2 red in H; dest_in.
  Qed.

  Lemma ObjsInvalid_init:
    ObjsInvalid (fun oidx => oidx <> rootOf topo) (implOStatesInit tr) (emptyMP Msg).
  Proof.
    unfold ObjsInvalid; intros.
    destruct (implOStatesInit tr)@[oidx] as [ost|] eqn:Host; simpl; auto.
    destruct (in_dec idx_dec oidx (c_li_indices cifc ++ c_l1_indices cifc));
      [|exfalso; rewrite implOStatesInit_None in Host by assumption; discriminate].
    rewrite c_li_indices_head_rootOf in i by assumption; inv i; [exfalso; auto|].
    rewrite implOStatesInit_value_non_root in Host by assumption; inv Host.
    apply ObjInvalid_init.
  Qed.

  Lemma msi_InvExcl_init:
    Invariant.InvInit impl (InvExcl topo cifc).
  Proof.
    do 2 (red; simpl); intros.
    destruct (implOStatesInit tr)@[eidx] as [eost|] eqn:Heost; simpl; auto.
    repeat ssplit.

    - red; intros.
      red in H; dest.
      destruct (in_dec idx_dec eidx (c_li_indices cifc ++ c_l1_indices cifc));
        [|exfalso; rewrite implOStatesInit_None in Heost by assumption; discriminate].
      rewrite c_li_indices_head_rootOf in i by assumption; inv i.
      + split.
        * red; intros.
          destruct (implOStatesInit tr)@[oidx] as [ost|] eqn:Host; simpl; auto.
          red.
          destruct (in_dec idx_dec oidx ((c_li_indices (snd (tree2Topo tr 0)))
                                           ++ c_l1_indices (snd (tree2Topo tr 0)))).
          { rewrite c_li_indices_head_rootOf in i by assumption.
            inv i; [exfalso; auto|].
            rewrite implOStatesInit_value_non_root in Host by assumption.
            inv Host.
            left; repeat split; [simpl; solve_msi..|].
            do 3 red; intros; do 2 red in H3; dest_in.
          }
          { rewrite implOStatesInit_None in Host by assumption.
            discriminate.
          }
        * do 3 red; intros; do 2 red in H1; dest_in.
      + exfalso.
        rewrite implOStatesInit_value_non_root in Heost by assumption.
        inv Heost.
        simpl in *; solve_msi.

    - red; intros.
      split; [|do 3 red; intros; do 2 red in H0; dest_in].

      destruct (in_dec idx_dec eidx (c_li_indices cifc ++ c_l1_indices cifc));
        [|rewrite implOStatesInit_None in Heost by assumption; discriminate].
      rewrite c_li_indices_head_rootOf in i by assumption; inv i.
      + red; intros.
        destruct (implOStatesInit tr)@[oidx] as [ost|] eqn:Host; simpl; auto.
        red.
        destruct (in_dec idx_dec oidx ((c_li_indices (snd (tree2Topo tr 0)))
                                         ++ c_l1_indices (snd (tree2Topo tr 0)))).
        * rewrite c_li_indices_head_rootOf in i by assumption.
          inv i.
          { elim H0.
            apply subtreeIndsOf_root_in.
            { apply tree2Topo_WfDTree. }
            { apply Subtree_refl. }
          }
          { rewrite implOStatesInit_value_non_root in Host by assumption.
            inv Host.
            left; repeat split; [simpl; solve_msi..|].
            do 3 red; intros; do 2 red in H2; dest_in.
          }
        * rewrite implOStatesInit_None in Host by assumption; discriminate.
      + rewrite implOStatesInit_value_non_root in Heost by assumption.
        destruct H.
        inv Heost; discriminate.

    - red; intros.
      destruct (in_dec idx_dec eidx (c_li_indices cifc ++ c_l1_indices cifc));
        [|rewrite implOStatesInit_None in Heost by assumption; discriminate].
      rewrite c_li_indices_head_rootOf in i by assumption; inv i.
      + rewrite implOStatesInit_value_root in Heost by assumption; inv Heost.
        split; [|intros; exfalso; cbn in H1; solve_msi].
        intros.
        eapply ObjsInvalid_impl; [apply ObjsInvalid_init|].
        simpl; intros.
        intro Hx; subst.
        eapply parent_not_in_subtree; eauto.
      + rewrite implOStatesInit_value_non_root in Heost by assumption; inv Heost.
        split; [|intros; exfalso; cbn in H2; solve_msi].
        intros.
        eapply ObjsInvalid_impl; [apply ObjsInvalid_init|].
        simpl; intros.
        intro Hx; subst.
        pose proof (parentIdxOf_child_indsOf _ _ H0).
        rewrite <-subtreeIndsOf_indsOf with (dtr:= fst (tree2Topo tr 0)) in H4;
          eauto; [|apply Subtree_refl].
        eapply subtreeIndsOf_In_each_other_eq in H4; eauto; subst.
        apply parentIdxOf_child_not_root in H0; auto.
  Qed.

  Lemma ObjsInvalid_ext_in:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall orqs,
        InObjInds tr 0 {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
        forall eins,
          ValidMsgsExtIn impl eins ->
          ObjsInvalid inP oss (enqMsgs eins msgs).
  Proof.
    unfold ObjsInvalid; intros.
    specialize (H _ H2).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct H.
    - left.
      red in H; dest.
      repeat split; [assumption..|].
      apply MsgsP_other_midx_enqMsgs; [assumption|].
      destruct H1; simpl.
      eapply DisjList_SubList; [eassumption|].
      eapply DisjList_comm, DisjList_SubList.
      + eapply SubList_trans;
          [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= oidx)].
        * solve_SubList.
        * specialize (H0 oidx); simpl in H0.
          rewrite Host in H0; simpl in H0.
          eassumption.
      + apply tree2Topo_minds_merqs_disj.
    - right.
      destruct H as [idm ?]; dest.
      exists idm; split; [|assumption].
      apply InMP_or_enqMsgs; auto.
  Qed.

  Lemma msi_InvExcl_ext_in:
    forall oss orqs msgs,
      InvExcl topo cifc {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      InObjInds tr 0 {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        InvExcl topo cifc {| st_oss := oss;
                             st_orqs := orqs;
                             st_msgs := enqMsgs eins msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.

    assert (NoCohMsgs eidx msgs ->
            NoCohMsgs eidx (enqMsgs eins msgs)) as Hnc.
    { intros.
      apply MsgsP_other_midx_enqMsgs; [assumption|].
      destruct H1; simpl.
      eapply DisjList_SubList; [eassumption|].
      eapply DisjList_comm, DisjList_SubList.
      { eapply SubList_trans;
          [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= eidx)].
        { solve_SubList. }
        { specialize (H0 eidx); simpl in H0.
          rewrite Heost in H0; simpl in H0.
          eassumption.
        }
      }
      { apply tree2Topo_minds_merqs_disj. }
    }

    dest; repeat ssplit.

    - clear H2 H3.
      red; intros.
      destruct H2.
      apply MsgsP_enqMsgs_inv in H3.
      specialize (H (conj H2 H3)); dest.
      split.
      + eapply ObjsInvalid_ext_in; eauto.
      + apply Hnc; assumption.

    - clear H H3.
      red; intros.
      destruct H; disc_MsgsP H3.
      specialize (H2 (conj H H3)); dest; split.
      + eapply ObjsInvalid_ext_in; eauto.
      + apply Hnc; assumption.

    - clear H H2.
      red; intros.
      specialize (H3 H _ H2); dest.
      split; intros.
      + clear H4; specialize (H3 H5).
        eapply ObjsInvalid_ext_in; eauto.
      + clear H3; specialize (H4 H5).
        eapply ObjsInvalid_ext_in; eauto.
  Qed.

  Corollary msi_InvExcl_InvTrsIns: InvTrsIns impl (InvExcl topo cifc).
  Proof.
    red; intros.
    inv H1.
    eapply msi_InvExcl_ext_in; eauto.
    apply (msi_InObjInds H).
  Qed.

  Lemma ObjsInvalid_ext_out:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall orqs,
        InObjInds tr 0 {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
        forall (eouts: list (Id Msg)),
          ValidMsgsExtOut impl eouts ->
          ObjsInvalid inP oss (deqMsgs (idsOf eouts) msgs).
  Proof.
    unfold ObjsInvalid; intros.
    specialize (H _ H2).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct H.
    - left.
      red in H; dest.
      repeat split; [assumption..|].
      apply MsgsP_deqMsgs; assumption.
    - right.
      destruct H as [idm ?]; dest.
      exists idm; split; [|assumption].
      apply deqMsgs_InMP_midx; [assumption|].
      destruct H1.
      eapply DisjList_In_1.
      + eapply DisjList_SubList; [eassumption|].
        apply DisjList_comm, tree2Topo_minds_merss_disj.
      + eapply tree2Topo_obj_chns_minds_SubList with (oidx:= oidx).
        * specialize (H0 oidx); simpl in H0.
          rewrite Host in H0; simpl in H0.
          eassumption.
        * inv H3; rewrite H6.
          solve_SubList.
  Qed.

  Lemma msi_InvExcl_ext_out:
    forall oss orqs msgs,
      InvExcl topo cifc {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      InObjInds tr 0 {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      forall (eouts: list (Id Msg)),
        ValidMsgsExtOut impl eouts ->
        InvExcl topo cifc {| st_oss := oss;
                             st_orqs := orqs;
                             st_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.

    assert (NoRsI eidx (deqMsgs (idsOf eouts) msgs) -> NoRsI eidx msgs) as Hrsi.
    { intros.
      apply MsgsP_other_midx_deqMsgs_inv in H2; [assumption|].
      destruct H1.
      simpl; eapply DisjList_SubList; [eassumption|].
      eapply DisjList_comm, DisjList_SubList.
      { eapply SubList_trans;
          [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= eidx)].
        { solve_SubList. }
        { specialize (H0 eidx); simpl in H0.
          rewrite Heost in H0; simpl in H0.
          eassumption.
        }
      }
      { apply tree2Topo_minds_merss_disj. }
    }

    dest; repeat ssplit.

    - clear H2 H3.
      red; intros.
      destruct H2.
      apply Hrsi in H3.
      specialize (H (conj H2 H3)); dest.
      split.
      + eapply ObjsInvalid_ext_out; eauto.
      + apply MsgsP_deqMsgs; assumption.

    - clear H H3.
      red; intros.
      destruct H.
      apply Hrsi in H3.
      specialize (H2 (conj H H3)); dest; split.
      + eapply ObjsInvalid_ext_out; eauto.
      + apply MsgsP_deqMsgs; assumption.

    - clear H H2.
      red; intros.
      specialize (H3 H _ H2); dest.
      split; intros.
      + clear H4; specialize (H3 H5).
        eapply ObjsInvalid_ext_out; eauto.
      + clear H3; specialize (H4 H5).
        eapply ObjsInvalid_ext_out; eauto.
  Qed.

  Corollary msi_InvExcl_InvTrsOuts: InvTrsOuts impl (InvExcl topo cifc).
  Proof.
    red; intros.
    inv H1.
    eapply msi_InvExcl_ext_out; eauto.
    apply (msi_InObjInds H).
  Qed.

  Definition GetRqPred (oidx: IdxT) (eout: Id Msg): Prop :=
    idOf eout = rqUpFrom oidx ->
    (valOf eout).(msg_type) = MRq ->
    (valOf eout).(msg_id) = Spec.getRq -> False.

  Definition SetRqPred (oidx: IdxT) (eout: Id Msg): Prop :=
    idOf eout = rqUpFrom oidx ->
    (valOf eout).(msg_type) = MRq ->
    (valOf eout).(msg_id) = Spec.setRq -> False.

  Definition RsMPred (oidx: IdxT) (eout: Id Msg) (oss: OStates)
             (msgs: MessagePool Msg): Prop :=
    idOf eout = downTo oidx ->
    (valOf eout).(msg_type) = MRs ->
    (valOf eout).(msg_id) = msiRsM ->
    ObjsInvalid (fun idx => ~ In idx (subtreeIndsOf topo oidx)) oss msgs.

  Definition DownRsSPred (oidx: IdxT) (eout: Id Msg) (oss: OStates)
             (msgs: MessagePool Msg): Prop :=
    idOf eout = rsUpFrom oidx ->
    (valOf eout).(msg_type) = MRs ->
    (valOf eout).(msg_id) = msiDownRsS ->
    ost <+- oss@[oidx]; (ost#[status] <= msiS /\ ost#[owned] = false).

  Definition DownRsISPred (oidx: IdxT) (eout: Id Msg) (oss: OStates)
             (msgs: MessagePool Msg): Prop :=
    idOf eout = rsUpFrom oidx ->
    (valOf eout).(msg_type) = MRs ->
    (valOf eout).(msg_id) = msiDownRsIS ->
    (ost <+- oss@[oidx]; ost#[status] <= msiI /\ ost#[owned] = false) /\
    ObjsInvalid (fun idx => In idx (subtreeIndsOf topo oidx)) oss msgs.

  Definition DownRsIMPred (oidx: IdxT) (eout: Id Msg) (oss: OStates)
             (msgs: MessagePool Msg): Prop :=
    idOf eout = rsUpFrom oidx ->
    (valOf eout).(msg_type) = MRs ->
    (valOf eout).(msg_id) = msiDownRsIM ->
    (ost <+- oss@[oidx]; ost#[status] <= msiI /\
                         ost#[dir].(dir_st) = msiI /\
                         ost#[owned] = false) /\
    ObjsInvalid
      (fun idx =>
         exists cidx,
           parentIdxOf topo cidx = Some oidx /\
           In idx (subtreeIndsOf topo cidx)) oss msgs.

  Definition InvRqPred (oidx: IdxT) (eout: Id Msg) (oss: OStates)
             (msgs: MessagePool Msg): Prop :=
    idOf eout = rqUpFrom oidx ->
    (valOf eout).(msg_type) = MRq ->
    (valOf eout).(msg_id) = msiInvRq ->
    ost <+- oss@[oidx]; ost#[dir].(dir_st) = msiI.

  Definition InvWRqPred (oidx: IdxT) (eout: Id Msg) (oss: OStates)
             (msgs: MessagePool Msg): Prop :=
    idOf eout = rqUpFrom oidx ->
    (valOf eout).(msg_type) = MRq ->
    (valOf eout).(msg_id) = msiInvWRq ->
    ost <+- oss@[oidx]; ost#[dir].(dir_st) = msiI.

  Definition InvExclMsgOutPred: MsgOutPred :=
    fun eout oss orqs msgs =>
      forall oidx,
        GetRqPred oidx eout /\ SetRqPred oidx eout /\
        RsMPred oidx eout oss msgs /\
        DownRsSPred oidx eout oss msgs /\
        DownRsISPred oidx eout oss msgs /\ DownRsIMPred oidx eout oss msgs /\
        InvRqPred oidx eout oss msgs /\ InvWRqPred oidx eout oss msgs.

  Lemma InvExclMsgOutPred_good:
    GoodMsgOutPred topo InvExclMsgOutPred.
  Proof.
    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    red; intros; split.

    - (* No RqDown predicates at all *)
      red; intros; destruct H.
      do 2 (red; intros).
      specialize (H2 oidx0); dest.
      repeat ssplit;
        try (red; intros; rewrite H11 in H1;
             derive_child_chns oidx; disc_rule_conds_ex; fail).

    - red; intros; destruct H.
      pose proof (rsEdgeUpFrom_Some (msi_RqRsChnsOnDTree tr) _ H0).
      destruct H1 as [rqUp [down [pidx ?]]]; dest.
      do 2 (red; intros).
      specialize (H4 oidx0); dest.
      repeat ssplit;
        try (red; intros; rewrite H13 in H0;
             derive_child_chns oidx; disc_rule_conds_ex; fail).

      + (* [DownRsSPred] *)
        red; intros; rewrite H13 in H0.
        derive_child_chns oidx; disc_rule_conds_ex.
        assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) oidx))
          by (eapply rqEdgeUpFrom_subtreeIndsOf_self_in;
              [eauto|congruence]).
        pose proof (H5 _ H16); dest.
        rewrite <-H17; apply H8; assumption.

      + (* [DownRsISPred] *)
        red; intros; rewrite H13 in H0.
        derive_child_chns oidx; disc_rule_conds_ex.
        split.
        * assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) oidx))
            by (eapply rqEdgeUpFrom_subtreeIndsOf_self_in;
                [eauto|congruence]).
          pose proof (H5 _ H16); dest.
          rewrite <-H17; apply H9; assumption.
        * red; intros.
          specialize (H9 H13 H14 H15); destruct H9 as [? ?].
          specialize (H17 _ H16).
          specialize (H5 _ H16); dest.
          rewrite <-H5.
          assert (exists pidx0, parentIdxOf (fst (tree2Topo tr 0)) oidx0 = Some pidx0).
          { eapply subtreeIndsOf_in_has_parent with (oidx:= oidx); eauto. }
          destruct H20 as [pidx0 ?].
          derive_child_chns oidx0.

          red in H19; dest.
          specialize (H19 _ H21).
          specialize (H24 _ H22).
          specialize (H25 _ H23).
          destruct (oss1@[oidx0]) as [ost0|]; simpl in *; auto.
          destruct H17; [left|right].
          { destruct H17 as [? [? ?]].
            repeat split; [assumption..|].
            apply not_MsgExistsSig_MsgsNotExist; intros.
            eapply MsgExistsSig_MsgsNotExist_false in H27; eauto.
            dest_in.
            all: try (destruct H29 as [[midx msg] [? ?]];
                      exists (midx, msg); split; [|assumption]; inv H29;
                      do 2 red in H28; do 2 red; simpl in *; congruence).
          }
          { destruct H17 as [[midx msg] [? ?]].
            exists (midx, msg); split; [|assumption]; inv H26.
            do 2 red in H17; do 2 red; simpl in *; congruence.
          }

      + (* [DownRsIMPred] *)
        red; intros; rewrite H13 in H0.
        derive_child_chns oidx; disc_rule_conds_ex.
        split.
        * assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) oidx))
            by (eapply rqEdgeUpFrom_subtreeIndsOf_self_in;
                [eauto|congruence]).
          pose proof (H5 _ H16); dest.
          rewrite <-H17; apply H10; assumption.
        * red; intros.
          specialize (H10 H13 H14 H15); destruct H10 as [? ?].
          specialize (H17 _ H16).
          destruct H16 as [cidx [? ?]].
          eapply subtreeIndsOf_child_SubList in H18; eauto.
          specialize (H5 _ H18); dest.
          rewrite <-H5.
          assert (exists pidx0, parentIdxOf (fst (tree2Topo tr 0)) oidx0 = Some pidx0).
          { eapply subtreeIndsOf_in_has_parent with (oidx:= oidx); eauto. }
          destruct H21 as [pidx0 ?].
          derive_child_chns oidx0.

          red in H20; dest.
          specialize (H20 _ H22).
          specialize (H25 _ H23).
          specialize (H26 _ H24).
          destruct (oss1@[oidx0]) as [ost0|]; simpl in *; auto.
          destruct H17; [left|right].
          { destruct H17 as [? [? ?]].
            repeat split; [assumption..|].
            apply not_MsgExistsSig_MsgsNotExist; intros.
            eapply MsgExistsSig_MsgsNotExist_false in H29; eauto.
            dest_in.
            all: try (destruct H30 as [[midx msg] [? ?]];
                      exists (midx, msg); split; [|assumption]; inv H30;
                      do 2 red in H29; do 2 red; simpl in *; congruence).
          }
          { destruct H17 as [[midx msg] [? ?]].
            exists (midx, msg); split; [|assumption]; inv H27.
            do 2 red in H17; do 2 red; simpl in *; congruence.
          }
  Qed.
  Local Hint Resolve InvExclMsgOutPred_good.

  Ltac disc_rule_custom ::=
    try disc_AtomicInv;
    try match goal with
        | [H: idsOf _ = map fst (rqi_rss _) |- _] => rewrite <-H in *
        | [H: SubList (_ :: _) _ |- _] => apply SubList_cons_inv in H; destruct H
        end.

  (*! Ltacs about [InvExcl] *)

  Ltac case_InvExcl_me_others :=
    match goal with
    | |- InvExcl _ _ _ => red; simpl; intros; mred; simpl
    end.

  Ltac case_InvObjOwned :=
    match goal with
    | [H: InvObjOwned _ _ _ _ _ |- InvObjOwned _ _ _ _ _] =>
      let Ho := fresh "H" in
      let Hrsi := fresh "H" in
      red; simpl; intros [Ho Hrsi]; disc_MsgsP Hrsi;
      specialize (H (conj Ho Hrsi)); dest;
      split; [red; intros; mred; simpl|]
    end.

  Ltac case_ObjInvalid_with oidx :=
    match goal with
    | |- ObjInvalid ?eidx _ _ =>
      destruct (idx_dec eidx oidx); subst
    end.

  Ltac case_ObjInvalid :=
    match goal with
    | [H: ObjInvalid _ _ _ |- ObjInvalid _ _ _] =>
      destruct H; [left|right]
    end.

  Ltac disc_InvExcl oidx :=
    repeat
      match goal with
      | [H: InvExcl _ _ _ |- _] => specialize (H oidx); simpl in H
      | [He: _ <+- ?ov; _, Ho: ?ov = Some _ |- _] =>
        rewrite Ho in He; simpl in He; dest; repeat ssplit
      end.

  Ltac disc_InvExcl_this :=
    match goal with
    | |- InvObjExcl0 ?oidx _ _ _ /\ _ => disc_InvExcl oidx
    end.

  Ltac disc_InvExcl_others :=
    match goal with
    | [H: InvExcl _ _ _ |- _ <+- _@[?eidx]; _] =>
      specialize (H eidx); simpl in H;
      disc_bind_true; dest; repeat ssplit
    end.

  Ltac disc_ObjsInvalid :=
    match goal with
    | [H: ObjsInvalid _ _ _ |- ObjsInvalid _ _ _] =>
      let Hi := fresh "H" in
      red; intros ? Hi; specialize (H _ Hi); mred;
      simpl in *; [|disc_bind_true]
    end.

  Ltac disc_ObjsInvalid_by oidx :=
    match goal with
    | [Hi: ObjsInvalid _ _ _ |- _] =>
      pose proof (Hi oidx ltac:(auto)); disc_bind_true
    end.

  Ltac disc_InvObjExcl0 :=
    match goal with
    | |- InvObjExcl0 _ _ _ _ =>
      let He := fresh "H" in
      red; intros He; disc_ObjExcl0_msgs He
    end.

  Ltac disc_InvObjExcl0_apply :=
    match goal with
    | [H: InvObjExcl0 _ _ _ _ |- InvObjExcl0 _ _ _ _] =>
      let He := fresh "H" in
      red; intros He; disc_ObjExcl0_msgs He;
      specialize (H He); dest
    end.

  Ltac disc_ObjExcl0 :=
    match goal with
    | [H: ObjExcl0 _ _ _ |- _] => red in H; dest; simpl in *
    end.

  Ltac derive_not_InvalidObj_not_in roidx :=
    match goal with
    | [H: ObjsInvalid (fun _ => ~ In _ ?inds) _ _ |- _] =>
      assert (In roidx inds)
        by (destruct (in_dec idx_dec roidx inds); [assumption|];
            exfalso;
            eapply ObjsInvalid_obj_status_false with (oidx:= roidx); eauto;
            simpl; solve_msi)
    end.

  Ltac solve_InvObjExcl0_by_ObjExcl0_false :=
    red; intros; exfalso;
    try match goal with
        | [H: context [invalidate ?st] |- _] =>
          pose proof (invalidate_sound st)
        | |- context [invalidate ?st] =>
          pose proof (invalidate_sound st)
        end;
    match goal with
    | [H: ObjExcl0 _ _ _ |- _] =>
      red in H; dest; simpl in *; solve_msi
    end.

  Local Hint Extern 0 (WfDTree _) => apply msi_WfDTree.
  Local Hint Extern 0 (RqRsChnsOnDTree _) => apply msi_RqRsChnsOnDTree.
  Ltac solve_by_topo_false :=
    match goal with
    | [H: ~ In ?oidx (subtreeIndsOf _ ?oidx) |- _] =>
      elim H; eapply parent_subtreeIndsOf_self_in; eauto; fail
    | [H: ~ In ?oidx (subtreeIndsOf _ ?oidx) |- _] =>
      elim H; eapply rqEdgeUpFrom_subtreeIndsOf_self_in; eauto; congruence
    | [Hp: parentIdxOf _ ?cidx = Some ?pidx, Hi: ~ In ?cidx (subtreeIndsOf _ ?oidx) |- _] =>
      elim Hi; apply subtreeIndsOf_child_in; auto; fail
    | [Hp: parentIdxOf _ ?cidx = Some ?pidx, Hip: In ?pidx (subtreeIndsOf _ ?oidx), Hic: ~ In ?cidx (subtreeIndsOf _ ?oidx) |- _] =>
      elim Hic; eapply inside_child_in; eauto; fail
    | [H: ~ In (l1ExtOf ?oidx) (subtreeIndsOf _ ?oidx) |- _] =>
      elim H; apply subtreeIndsOf_child_in; auto;
      apply tree2Topo_l1_ext_parent; assumption

    | [Hp1: parentIdxOf _ ?rcidx1 = Some ?pidx,
            Hp2: parentIdxOf _ ?rcidx2 = Some ?pidx,
                 Hc: ?rcidx1 <> ?rcidx2,
                     Hin: In ?rcidx1 (subtreeIndsOf _ ?rcidx2) |- _] =>
      eapply subtreeIndsOf_other_child_not_in with (cidx1:= rcidx1) (cidx2:= rcidx2); eauto
    | [Hp1: parentIdxOf _ ?rcidx1 = Some ?pidx,
            Hp2: parentIdxOf _ ?rcidx2 = Some ?pidx,
                 Hc: ?rcidx2 <> ?rcidx1,
                     Hin: In ?rcidx1 (subtreeIndsOf _ ?rcidx2) |- _] =>
      eapply subtreeIndsOf_other_child_not_in with (cidx1:= rcidx1) (cidx2:= rcidx2); eauto
    | [Hp: parentIdxOf _ ?cidx = Some ?pidx,
           Hin: In ?pidx (subtreeIndsOf _ ?cidx) |- _] =>
      eapply parent_not_in_subtree; eauto


    | [Hp: parentIdxOf _ ?cidx = Some ?pidx,
           Hn: ~ In ?pidx (subtreeIndsOf _ ?sidx),
               Hin: In ?cidx (subtreeIndsOf _ ?sidx) |- _] =>
      eapply outside_child_in in Hn; eauto;
      destruct Hn; [subst|exfalso; auto]; disc_rule_conds_ex; fail
    | [Hp: parentIdxOf _ ?cidx = Some ?pidx,
           Hn: ~ In ?pidx (subtreeIndsOf _ ?sidx),
               Hin: In ?cidx (subtreeIndsOf _ ?sidx),
                    Hneq: ?cidx <> ?sidx |- _] =>
      elim Hn; eapply inside_parent_in with (cidx:= cidx); eauto
    | [Hp: parentIdxOf _ ?cidx = Some ?pidx,
           Hn: ~ In ?pidx (subtreeIndsOf _ ?sidx),
               Hin: In ?cidx (subtreeIndsOf _ ?sidx),
                    Hneq: ?sidx <> ?cidx |- _] =>
      elim Hn; eapply inside_parent_in with (cidx:= cidx); eauto
    end.

  Ltac solve_ObjInvalid0 :=
    match goal with
    | [H: ObjInvalid0 _ _ _ |- ObjInvalid0 _ _ _] =>
      destruct H as [? [? ?]]; repeat split; [assumption..|solve_MsgsP]
    end.

  Ltac solve_ObjInvRs :=
    repeat
      match goal with
      | [H: ObjInvRs _ _ |- ObjInvRs _ _] =>
        let midx := fresh "midx" in
        let msg := fresh "msg" in
        destruct H as [[midx msg] [? ?]];
        exists (midx, msg); split; [|assumption]
      | [H: sigOf _ = _ |- _] => inv H
      | |- InMPI (enqMP _ _ _) _ => apply InMP_or_enqMP; right
      | |- InMP _ _ (enqMP _ _ _) => apply InMP_or_enqMP; right
      | |- InMPI (deqMP _ _) _ => apply deqMP_InMP_midx; [|solve_chn_not_in]
      | |- InMP _ _ (deqMP _ _) => apply deqMP_InMP_midx; [|solve_chn_not_in]
      | _ => assumption
      end.

  Ltac solve_by_ObjsInvalid_status_false roidx :=
    exfalso;
    eapply ObjsInvalid_obj_status_false with (oidx := roidx); eauto;
    simpl in *; solve [auto|solve_msi].

  Ltac solve_by_ObjsInvalid_dir_false roidx :=
    exfalso;
    eapply ObjsInvalid_obj_dir_false with (oidx := roidx); eauto;
    simpl in *; solve [auto|solve_msi].

  Ltac solve_by_ObjsInvalid_rsS_false roidx :=
    exfalso;
    eapply ObjsInvalid_rsS_false with (oidx:= roidx); eauto;
    apply FirstMP_InMP; assumption.

  Ltac solve_by_ObjsInvalid_rsM_false roidx :=
    exfalso;
    match goal with
    | [H: ObjsInvalid _ _ _ |- _] =>
      eapply ObjsInvalid_rsM_false with (oidx:= roidx);
      [eapply H|..]; simpl in *; eauto;
      apply FirstMP_InMP; assumption
    end.

  Ltac solve_by_ObjsInvalid_downRsS_false roidx :=
    exfalso;
    match goal with
    | [H: ObjsInvalid _ _ _ |- _] =>
      eapply ObjsInvalid_downRsS_false with (oidx:= roidx);
      [eapply H|..]; simpl in *; eauto;
      apply FirstMP_InMP; assumption
    end.

  Ltac solve_by_ObjsInvalid_downRsIM_false roidx :=
    exfalso;
    match goal with
    | [H: ObjsInvalid _ _ _ |- _] =>
      eapply ObjsInvalid_downRsIM_false with (oidx:= roidx);
      [eapply H|..]; simpl in *; eauto;
      apply FirstMP_InMP; assumption
    end.

  Ltac solve_InvObjOwned_by_false :=
    red; simpl; intros [? ?]; discriminate.

  Ltac split_InvDirInv_apply :=
    match goal with
    | [H: InvDirInv _ _ _ _ _ _ |- InvDirInv _ _ _ _ _ _] =>
      let Hli := fresh "H" in
      let Hc := fresh "H" in
      red; intros Hli ? Hc;
      let H1 := fresh "H" in
      let H2 := fresh "H" in
      specialize (H Hli _ Hc); destruct H as [H1 H2];
      let Hdir := fresh "H" in
      split; intros Hdir; [specialize (H1 Hdir)|specialize (H2 Hdir)]
    end.

  Ltac split_InvDirInv :=
    match goal with
    | [H: InvDirInv _ _ _ _ _ _ |- InvDirInv _ _ _ _ _ _] =>
      let Hli := fresh "H" in
      let Hc := fresh "H" in
      red; intros Hli ? Hc;
      specialize (H Hli _ Hc); dest; split; intros
    end.

  Lemma ObjsInvalid_deq_sound:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall rmsgs,
        NoDup (idsOf rmsgs) ->
        Forall (FirstMPI msgs) rmsgs ->
        Forall (fun idm => In (msg_id (valOf idm))
                              [msiRqS; msiDownRqS;
                              msiRqM; msiDownRqIS; msiDownRqIM; msiDownRsIS;
                              msiInvRq; msiInvWRq;
                              getRq; getRs; setRq; setRs]) rmsgs ->
        ObjsInvalid inP oss (deqMsgs (idsOf rmsgs) msgs).
  Proof.
    red; intros.
    specialize (H _ H3).
    disc_bind_true.
    case_ObjInvalid.
    - solve_ObjInvalid0.
    - solve_ObjInvRs.
      apply deqMsgs_InMP; try assumption.
      simpl; intro Hx.
      rewrite Forall_forall in H2; specialize (H2 _ Hx).
      simpl in H2; rewrite H9 in H2.
      intuition discriminate.
  Qed.

  Lemma ObjsInvalid_enq_sound:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall nmsgs,
        Forall (fun idm => In (msg_id (valOf idm))
                              [msiRqS; msiDownRqS;
                              msiRqM; msiDownRqIS; msiDownRqIM; msiDownRsIS;
                              msiInvRq; msiInvWRq; msiInvRs;
                              getRq; getRs; setRq; setRs]) nmsgs ->
        ObjsInvalid inP oss (enqMsgs nmsgs msgs).
  Proof.
    red; intros.
    specialize (H _ H1).
    disc_bind_true.
    case_ObjInvalid.
    - solve_ObjInvalid0.
      apply MsgsP_other_msg_id_enqMsgs; [assumption|].
      simpl.
      apply (DisjList_spec_1 idx_dec); intros midx ?.
      apply in_map_iff in H5; destruct H5 as [[rmidx msg] [? ?]].
      simpl in *; subst.
      rewrite Forall_forall in H0; specialize (H0 _ H6); simpl in H0.
      intro Hx.
      repeat
        match goal with
        | [H: _ \/ _ |- _] => destruct H
        | [H1: _ = msg_id ?msg, H2: _ = msg_id ?msg |- _] =>
          rewrite <-H1 in H2; discriminate
        | [H: False |- False] => auto
        end.
    - solve_ObjInvRs.
      apply InMP_or_enqMsgs; auto.
  Qed.

  Lemma InvExcl_deq_sound:
    forall oss porqs norqs msgs,
      InvExcl topo cifc {| st_oss := oss; st_orqs := porqs; st_msgs := msgs |} ->
      forall rmsgs,
        NoDup (idsOf rmsgs) ->
        Forall (FirstMPI msgs) rmsgs ->
        Forall (fun idm => In (msg_id (valOf idm))
                              [msiRqS; msiDownRqS;
                              msiRqM; msiDownRqIS; msiDownRqIM; msiDownRsIS;
                              msiInvRq; msiInvWRq;
                              getRq; getRs; setRq; setRs]) rmsgs ->
        InvExcl topo cifc {| st_oss := oss;
                             st_orqs := norqs;
                             st_msgs := deqMsgs (idsOf rmsgs) msgs |}.
  Proof.
    intros.
    red; simpl; intros.
    specialize (H eidx); simpl in H.

    assert (NoRsI eidx (deqMsgs (idsOf rmsgs) msgs) ->
            NoRsI eidx msgs) as Hrsi.
    { intros.
      apply MsgsP_other_msg_id_deqMsgs_inv in H3; try eassumption.
      simpl.
      apply (DisjList_spec_1 idx_dec); intros midx ?.
      apply in_map_iff in H4; destruct H4 as [[rmidx msg] [? ?]].
      simpl in *; subst.
      rewrite Forall_forall in H2; specialize (H2 _ H5); simpl in H2.
      intro Hx; destruct Hx; [|auto].
      rewrite <-H4 in H2.
      intuition discriminate.
    }

    disc_bind_true; dest; repeat ssplit.

    - red; intros.
      destruct H6.
      apply Hrsi in H7.
      specialize (H (conj H6 H7)); dest; split.
      + apply ObjsInvalid_deq_sound; auto.
      + solve_MsgsP.
    - red; intros.
      destruct H6.
      apply Hrsi in H7.
      specialize (H4 (conj H6 H7)); dest; split.
      + apply ObjsInvalid_deq_sound; auto.
      + solve_MsgsP.
    - red; intros.
      specialize (H5 H6 _ H7); dest.
      split; intros.
      + specialize (H5 H9).
        apply ObjsInvalid_deq_sound; auto.
      + specialize (H8 H9).
        apply ObjsInvalid_deq_sound; auto.
  Qed.

  Lemma InvExcl_enq_sound:
    forall oss porqs norqs msgs,
      InvExcl topo cifc {| st_oss := oss; st_orqs := porqs; st_msgs := msgs |} ->
      forall nmsgs,
        Forall (fun idm => In (msg_id (valOf idm))
                              [msiRqS; msiDownRqS;
                              msiRqM; msiDownRqIS; msiDownRqIM; msiDownRsIS;
                              msiInvRq; msiInvWRq; msiInvRs;
                              getRq; getRs; setRq; setRs]) nmsgs ->
        InvExcl topo cifc {| st_oss := oss;
                             st_orqs := norqs;
                             st_msgs := enqMsgs nmsgs msgs |}.
  Proof.
    intros.
    red; simpl; intros.
    specialize (H eidx); simpl in H.

    assert (NoCohMsgs eidx msgs ->
            NoCohMsgs eidx (enqMsgs nmsgs msgs)) as Hnc.
    { intros.
      apply MsgsP_other_msg_id_enqMsgs; [assumption|].
      simpl.
      apply (DisjList_spec_1 idx_dec); intros midx ?.
      apply in_map_iff in H2; destruct H2 as [[rmidx msg] [? ?]].
      simpl in *; subst.
      rewrite Forall_forall in H0; specialize (H0 _ H3); simpl in H0.
      intro Hx.
      repeat
        match goal with
        | [H: _ \/ _ |- _] => destruct H
        | [H1: _ = msg_id ?msg, H2: _ = msg_id ?msg |- _] =>
          rewrite <-H1 in H2; discriminate
        | [H: False |- False] => auto
        end.
    }

    disc_bind_true; dest; repeat ssplit.

    - disc_InvObjExcl0_apply; split.
      + apply ObjsInvalid_enq_sound; auto.
      + apply Hnc; assumption.

    - red; intros.
      destruct H4; disc_MsgsP H5.
      specialize (H2 (conj H4 H5)); dest; split.
      + apply ObjsInvalid_enq_sound; auto.
      + apply Hnc; assumption.

    - red; intros.
      specialize (H3 H4 _ H5); dest.
      split; intros.
      + specialize (H3 H7).
        apply ObjsInvalid_enq_sound; auto.
      + specialize (H6 H7).
        apply ObjsInvalid_enq_sound; auto.
  Qed.

  Lemma ObjsInvalid_state_transition_sound:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall oidx (post nost: OState),
        oss@[oidx] = Some post ->
        (nost#[status] <= msiI \/ nost#[status] <= post#[status]) ->
        (nost#[dir].(dir_st) <> msiS \/ nost#[dir].(dir_st) = post#[dir].(dir_st)) ->
        ObjsInvalid inP (oss +[oidx <- nost]) msgs.
  Proof.
    intros.
    red; intros.
    specialize (H _ H3).
    mred; simpl; auto.
    destruct H; [left|right].
    - destruct H as [? [? ?]].
      repeat split.
      + solve_msi.
      + destruct H2; [assumption|congruence].
      + assumption.
    - assumption.
  Qed.

  Lemma InvExcl_state_transition_sound:
    forall oss porqs msgs,
      InvExcl topo cifc {| st_oss := oss; st_orqs := porqs; st_msgs := msgs |} ->
      forall oidx (post nost: OState) norqs,
        oss@[oidx] = Some post ->
        (nost#[status] <= msiI \/ nost#[status] <= post#[status]) ->
        post#[owned] || negb (nost#[owned]) = true ->
        nost#[dir] = post#[dir] ->
        InvExcl topo cifc {| st_oss := oss +[oidx <- nost];
                             st_orqs := norqs; st_msgs := msgs |}.
  Proof.
    intros.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    mred; simpl; dest.
    - repeat ssplit.
      + red; intros.
        destruct H6.
        assert (msiM <= post#[status]) by solve_msi.
        specialize (H (conj H8 H7)); dest.
        split; [|assumption].
        eapply ObjsInvalid_state_transition_sound; eauto.
        intuition congruence.
      + red; intros.
        destruct H6.
        rewrite H6 in H2; simpl in H2.
        rewrite orb_false_r in H2.
        specialize (H4 (conj H2 H7)); dest; split; [|assumption].
        eapply ObjsInvalid_state_transition_sound; eauto.
        intuition congruence.
      + red; intros.
        specialize (H5 H6 _ H7); dest.
        split; intros.
        * rewrite <-H3 in H5; specialize (H5 H9).
          eapply ObjsInvalid_state_transition_sound; eauto.
          intuition congruence.
        * rewrite <-H3 in H8; specialize (H8 H9).
          eapply ObjsInvalid_state_transition_sound; eauto.
          intuition congruence.

    - disc_bind_true; dest; repeat ssplit.
      + red; intros; specialize (H H7); dest.
        split; [|assumption].
        eapply ObjsInvalid_state_transition_sound; eauto.
        simpl; intuition congruence.
      + red; intros.
        specialize (H5 H7); dest; split; [|assumption].
        eapply ObjsInvalid_state_transition_sound; eauto.
        simpl; intuition congruence.
      + red; intros.
        specialize (H6 H7 _ H8); dest.
        split; intros.
        * specialize (H6 H10).
          eapply ObjsInvalid_state_transition_sound; eauto.
          simpl; intuition congruence.
        * specialize (H9 H10).
          eapply ObjsInvalid_state_transition_sound; eauto.
          simpl; intuition congruence.
  Qed.

  Lemma InvExcl_inv_ObjsInvalid:
    forall oss orqs msgs
           (Hioi: InObjInds tr 0 {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |}),
      InvExcl topo cifc {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      forall oidx nost cidx cost uaddr,
        In cidx (c_li_indices cifc ++ c_l1_indices cifc) ->
        parentIdxOf topo cidx = Some oidx ->
        oss@[cidx] = Some cost ->
        cost#[dir].(dir_st) = msiI ->
        ObjsInvalid (fun idx => In idx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx))
                    (oss +[oidx <- nost])
                    (enqMP (downTo cidx) {| msg_id := msiInvRs;
                                            msg_type := MRs;
                                            msg_addr := uaddr;
                                            msg_value := 0 |}
                           (deqMP (rqUpFrom cidx) msgs)).
  Proof.
    intros.
    disc_InvExcl cidx.

    assert (ObjInvalid cidx cost
                       (enqMP (downTo cidx) {| msg_id := msiInvRs;
                                               msg_type := MRs;
                                               msg_addr := uaddr;
                                               msg_value := 0 |}
                              (deqMP (rqUpFrom cidx) msgs))) as Hoi.
    { right; eexists (_, _); split.
      { apply InMP_or_enqMP; left; simpl; eauto. }
      { reflexivity. }
    }

    apply in_app_or in H0; destruct H0.
    - eapply ObjsInvalid_in_composed with (oidx:= cidx).
      + apply parentIdxOf_not_eq in H1; auto; mred.
      + apply Hoi.
      + red; intros; destruct H6 as [ccidx [? ?]].
        specialize (H5 H0 _ H6); dest.
        specialize (H5 (getDir_st_I _ H3 _) _ H7).
        mred; simpl.
        * exfalso.
          eapply subtreeIndsOf_child_SubList in H7; eauto.
          eapply parent_not_in_subtree with (pidx:= oidx); eauto.
        * disc_bind_true.
          destruct H5; [left|right].
          { destruct H5 as [? [? ?]]; repeat split; [assumption..|].
            solve_MsgsP.
          }
          { destruct H5 as [[midx msg] [? ?]].
            exists (midx, msg); split; [|assumption]; inv H10.
            apply InMP_or_enqMP; right.
            apply deqMP_InMP_midx; [assumption|].
            simpl; intro Hx; discriminate.
          }

    - red; intros.
      mred; simpl; [exfalso; eapply parent_not_in_subtree with (pidx:= oidx); eauto|].
      rewrite tree2Topo_l1_subtreeIndsOf in H6 by assumption.
      dest_in; [rewrite H2; simpl; apply Hoi|].
      disc_bind_true.
      exfalso.
      specialize (Hioi (l1ExtOf cidx)); simpl in Hioi.
      rewrite H6 in Hioi; simpl in Hioi.
      eapply tree2Topo_l1_child_ext_not_in; eauto.
  Qed.

  Ltac solve_InvExcl_msgs :=
    repeat
      match goal with
      | _ => assumption
      (* For single enq/deq *)
      | |- NoDup (idsOf [_]) => repeat constructor; intro; dest_in
      | |- NoDup [_] => repeat constructor; intro; dest_in
      | |- Forall _ [_] => constructor; [|constructor]
      | |- In _ _ => simpl
      | [H: msg_id ?msg = _ |- context [msg_id ?msg]] => rewrite H
      | |- _ \/ _ => tauto
      (* For multiple enqs/deqs *)
      | [H: ValidMsgsIn _ ?msgs |- NoDup (idsOf ?msgs)] => apply H
      | |- Forall _ (map _ _) =>
        let midx := fresh "midx" in
        let msg := fresh "msg" in
        let Hin := fresh "H" in
        apply Forall_forall; intros [midx msg] Hin;
        apply in_map_iff in Hin; dest
      | [Hf: Forall (fun _ => msg_id _ = _) ?msgs
         |- Forall (fun _ => In _ _) ?msgs] =>
        let midx := fresh "midx" in
        let msg := fresh "msg" in
        let Hin := fresh "H" in
        apply Forall_forall; intros [midx msg] Hin;
        rewrite Forall_forall in Hf; specialize (Hf _ Hin);
        simpl in Hf
      | [H: (_, _) = (_, _) |- _] => inv H
      end.

  Ltac solve_InvExcl_trivial :=
    try match goal with
        | |- InvExcl _ _ {| st_oss := ?oss +[?oidx <- ?pos] |} =>
          replace (oss +[oidx <- pos]) with oss by meq
        end;
    repeat
      match goal with
      | [He: InvExcl _ _ {| st_orqs := ?orqs |}
         |- InvExcl _ _ {| st_msgs := enqMP ?midx ?msg _ |}] =>
        eapply InvExcl_enq_sound with (porqs:= orqs) (nmsgs:= [(midx, msg)]);
        [|solve_InvExcl_msgs; fail]
      | [He: InvExcl _ _ {| st_orqs := ?orqs |},
             Hf: FirstMPI _ (?midx, ?msg)
         |- InvExcl _ _ {| st_msgs := deqMP ?midx _ |}] =>
        eapply InvExcl_deq_sound with (porqs:= orqs) (rmsgs:= [(midx, msg)]);
        [|solve_InvExcl_msgs; fail..]
      | [He: InvExcl _ _ {| st_orqs := ?orqs |}
         |- InvExcl _ _ {| st_msgs := enqMsgs _ _ |}] =>
        eapply InvExcl_enq_sound with (porqs:= orqs); [|solve_InvExcl_msgs; fail]
      | [He: InvExcl _ _ {| st_orqs := ?orqs |}
         |- InvExcl _ _ {| st_msgs := deqMsgs _ _ |}] =>
        eapply InvExcl_deq_sound with (porqs:= orqs); [|solve_InvExcl_msgs; fail..]
      end; try eassumption.

  Ltac exfalso_InvTrs_init :=
    exfalso;
    repeat
      match goal with
      | [H: In _ (c_merqs _) |- _] =>
        rewrite c_merqs_l1_rqUpFrom in H;
        apply in_map_iff in H;
        let oidx := fresh "oidx" in
        destruct H as [oidx [? ?]]
      | [H: parentIdxOf _ (l1ExtOf _) = Some _ |- _] =>
        rewrite tree2Topo_l1_ext_parent in H by assumption
      | [H: rqUpFrom (l1ExtOf _) = rqUpFrom _ |- _] => inv H
      | [H: rqUpFrom (l1ExtOf _) = rsUpFrom _ |- _] => inv H
      | [H: rqUpFrom (l1ExtOf _) = downTo _ |- _] => inv H
      | [H: Some _ = Some _ |- _] => inv H
      | [H1: ~ In ?i ?l, H2: In ?i ?l |- _] => elim H1; assumption
      end.

  Ltac pick_rsUp_single :=
    match goal with
    | [Hrr: RqRsDownMatch _ _ _ ?rss _, Hrss: [_] = map fst ?rss |- _] =>
      let Hrr0 := fresh "H" in
      pose proof Hrr as Hrr0;
      eapply RqRsDownMatch_rs_rq in Hrr0; [|rewrite <-Hrss; left; reflexivity];
      let cidx := fresh "cidx" in
      let down := fresh "down" in
      destruct Hrr0 as [cidx [down ?]]; dest
    end.

  Ltac pick_rsUps_one :=
    match goal with
    | [Hrr: RqRsDownMatch _ _ _ ?rss _, Hrss: idsOf ?ins = map fst ?rss |- _] =>
      pose proof (RqRsDownMatch_rs_not_nil Hrr);
      let midx := fresh "midx" in
      let msg := fresh "msg" in
      destruct ins as [|[midx msg] ins];
      [exfalso; apply eq_sym, map_eq_nil in Hrss; auto|];
      simpl in Hrr; eapply RqRsDownMatch_rs_rq in Hrr;
      [|rewrite <-Hrss; left; reflexivity];
      let cidx := fresh "cidx" in
      let down := fresh "down" in
      destruct Hrr as [cidx [down ?]]; dest
    end.

  Ltac case_idx_eq oidx1 oidx2 :=
    destruct (idx_dec oidx1 oidx2); [subst|].

  Ltac case_in_subtree oidx sidx :=
    destruct (in_dec idx_dec oidx (subtreeIndsOf (fst (tree2Topo tr 0)) sidx)).

  Ltac solve_ObjsInvalid_trivial :=
    repeat (first [assumption
                  |eapply ObjsInvalid_shrinked; eassumption
                  |eapply ObjsInvalid_this_enqMP_silent;
                   [| |simpl; tauto]; [|solve [auto|intro; solve_by_topo_false]]
                  |eapply ObjsInvalid_this_deqMP_silent;
                   [| |simpl; tauto]; [|solve [auto|intro; solve_by_topo_false]]
                  |apply ObjsInvalid_this_state_silent;
                   [|solve [auto|intro; solve_by_topo_false]]
                  |apply ObjsInvalid_enq_sound with (nmsgs:= [(_, _)]);
                   [|constructor; [simpl; tauto|constructor]]
                  |eapply ObjsInvalid_deq_sound with (rmsgs:= [(_, _)]);
                   [|eauto|eauto
                    |constructor; [simpl; intuition auto; fail|constructor]]
           ]).

  Ltac disc_InvObjOwned :=
    match goal with
    | [H: InvObjOwned _ _ _ _ _ |- InvObjOwned _ _ _ _ _] =>
      let Ho := fresh "H" in
      let Hrsi := fresh "H" in
      red; simpl; intros [Ho Hrsi];
      try (disc_MsgsP Hrsi; specialize (H (conj Ho Hrsi)); dest)
    end.

  Ltac solve_msg_pred_base :=
    let Hm := fresh "H" in
    red; simpl; intros Hm _ _; inv Hm; mred.

  Ltac solve_AtomicInv_init :=
    do 2 red; simpl;
    repeat constructor;
    try (red; simpl; intros; intuition discriminate);
    solve_msg_pred_base.

  Ltac disc_L1DirI oidx :=
    match goal with
    | [Hl: InvL1DirI _ {| st_oss := ?oss |},
           Hoin: In oidx (c_l1_indices _),
                 Host: ?oss@[oidx] = Some _ |- _] =>
      red in Hl; rewrite Forall_forall in Hl;
      specialize (Hl _ Hoin); simpl in Hl; rewrite Host in Hl
    end.

  Lemma msi_InvExcl_InvTrs_init:
    forall st1,
      Reachable (steps step_m) impl st1 ->
      InvExcl topo cifc st1 ->
      forall oidx ridx ins outs st2,
        SubList (idsOf ins) (sys_merqs impl) ->
        step_m impl st1 (RlblInt oidx ridx ins outs) st2 ->
        AtomicInv
          InvExclMsgOutPred
          ins st1 [RlblInt oidx ridx ins outs] outs st2 /\
        InvExcl topo cifc st2.
  Proof. (* SKIP_PROOF_ON
    intros.

    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    pose proof (footprints_ok
                  (msi_GoodORqsInit Htr)
                  (msi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (msi_InObjInds H) as Hioi.
    pose proof (msi_MsgConflictsInv
                  (@msi_RootChnInv_ok _ Htr) H) as Hpmcf.
    pose proof (@MsiUpLockInv_ok _ Htr _ H) as Hulinv.
    pose proof (@MsiDownLockInv_ok _ Htr _ H) as Hdlinv.
    pose proof (@msi_InvL1DirI_ok _ Htr _ H) as Hl1d.

    inv_step.

    simpl in H7; destruct H7; [subst|apply in_app_or in H2; destruct H2].

    - (*! Cases for the main memory *)

      (** Abstract the root. *)
      assert (In (rootOf (fst (tree2Topo tr 0)))
                 (c_li_indices (snd (tree2Topo tr 0)))) as Hin.
      { rewrite c_li_indices_head_rootOf by assumption.
        left; reflexivity.
      }

      remember (rootOf (fst (tree2Topo tr 0))) as oidx; clear Heqoidx.

      (** The root does not belong to [c_l1_indices]. *)
      assert (~ In oidx (c_l1_indices (snd (tree2Topo tr 0)))).
      { pose proof (tree2Topo_WfCIfc tr 0) as [? _].
        apply (DisjList_NoDup idx_dec) in H2.
        eapply DisjList_In_2; [eassumption|].
        assumption.
      }

      (** Do case analysis per a rule. *)
      apply concat_In in H8; destruct H8 as [crls [? ?]].
      apply in_map_iff in H3; destruct H3 as [cidx [? ?]]; subst.

      (** Derive that the child has the parent. *)
      assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
        by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

      dest_in; disc_rule_conds_ex.
      all: try (exfalso_InvTrs_init; fail).

    - (*! Cases for Li caches *)
      apply in_map_iff in H2; destruct H2 as [oidx [? ?]]; subst; simpl in *.

      pose proof (c_li_indices_tail_has_parent Htr _ _ H3).
      destruct H2 as [pidx [? ?]].
      pose proof (Htn _ _ H4); dest.

      (** The object index does not belong to [c_l1_indices]. *)
      assert (~ In oidx (c_l1_indices (snd (tree2Topo tr 0)))).
      { pose proof (tree2Topo_WfCIfc tr 0) as [? _].
        apply (DisjList_NoDup idx_dec) in H9.
        eapply DisjList_In_2; [eassumption|].
        apply tl_In; assumption.
      }

      (** Do case analysis per a rule. *)
      apply in_app_or in H8; destruct H8.

      1: { (** Rules per a child *)
        apply concat_In in H8; destruct H8 as [crls [? ?]].
        apply in_map_iff in H8; destruct H8 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in; disc_rule_conds_ex.
        all: try (exfalso_InvTrs_init; fail).
      }

      dest_in; disc_rule_conds_ex.

      all: try (derive_footprint_info_basis oidx; exfalso_InvTrs_init; fail).

      { disc_MsiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx.
        disc_responses_from.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }
      { disc_MsiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx; [solve_midx_false|].
        disc_responses_from.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }

      { disc_MsiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx.
        pick_rsUps_one.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }
      { disc_MsiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx.
        pick_rsUps_one.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }

      { disc_MsiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx; [solve_midx_false|].
        pick_rsUps_one.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }
      { disc_MsiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx; [solve_midx_false|].
        pick_rsUps_one.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }
      { disc_MsiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx; [solve_midx_false|].
        pick_rsUps_one.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }

      { (* [liInvRqUpUp] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_init. }
        { solve_InvExcl_trivial. }
      }

      { (* [liInvRqUpUpWB] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_init. }
        { solve_InvExcl_trivial. }
      }

      { (* [liPushImm] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_init. }
        { eapply InvExcl_state_transition_sound with (porqs:= orqs);
            try eassumption.
          { simpl; intuition solve_msi. }
          { simpl; intuition. }
          { reflexivity. }
        }
      }

    - (*! Cases for L1 caches *)
      apply in_map_iff in H2; destruct H2 as [oidx [? ?]]; subst.

      pose proof (c_l1_indices_has_parent Htr _ _ H3).
      destruct H2 as [pidx [? ?]].
      pose proof (Htn _ _ H4); dest.

      (** Do case analysis per a rule. *)
      dest_in.

      { (* [l1GetSImm] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_init. }
        { solve_InvExcl_trivial. }
      }

      { (* [l1GetSRqUpUp] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_init. }
        { solve_InvExcl_trivial. }
      }

      { (* [l1GetSRsDownDownS] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        exfalso_InvTrs_init.
      }

      { (* [l1DownSImm] *)
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }

      { (* [l1GetMImm] *)
        disc_rule_conds_ex.
        derive_NoRsI_by_no_uplock oidx msgs.

        split.
        { solve_AtomicInv_init. }
        { solve_InvExcl_trivial.
          case_InvExcl_me_others.
          { assert (ObjExcl0 oidx os msgs)
              by (split; [simpl in *; solve_msi|assumption]).
            disc_InvExcl_this.
            { specialize (H0 H14); dest.
              red; intros.
              split; [|assumption].
              red; intros; specialize (H0 _ H27); mred.
            }
            { specialize (H0 H14); dest.
              red; intros _.
              split; [|assumption].
              red; intros.
              mred; [solve_by_topo_false|auto].
            }
            { red; intros; exfalso.
              pose proof (tree2Topo_WfCIfc tr 0) as [? _].
              apply (DisjList_NoDup idx_dec) in H27.
              eapply DisjList_In_1; eassumption.
            }
          }

          { disc_InvExcl_others.
            { disc_InvObjExcl0_apply.
              solve_by_ObjsInvalid_status_false oidx.
            }
            { case_InvObjOwned; auto.
              solve_by_ObjsInvalid_status_false oidx.
            }
            { split_InvDirInv_apply.
              { case_in_subtree oidx cidx.
                { solve_by_ObjsInvalid_status_false oidx. }
                { apply ObjsInvalid_this_state_silent; auto. }
              }
              { case_in_subtree oidx cidx.
                { apply ObjsInvalid_this_state_silent; auto. }
                { solve_by_ObjsInvalid_status_false oidx. }
              }
            }
          }
        }
      }

      { (* [l1GetMRqUpUp] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_init. }
        { solve_InvExcl_trivial. }
      }

      { (* [l1GetMRsDownDown] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        exfalso_InvTrs_init.
      }

      { (* [l1DownIImmS] *)
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }
      { (* [l1DownIImmM] *)
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }

      { (* [l1InvRqUpUp] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_init.
          disc_L1DirI oidx0; assumption.
        }
        { solve_InvExcl_trivial. }
      }

      { (* [l1InvRqUpUpWB] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_init.
          disc_L1DirI oidx0; assumption.
        }
        { solve_InvExcl_trivial. }
      }

      { (* [l1InvRsDownDown] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        exfalso_InvTrs_init.
      }

      Unshelve.
      all: assumption.

      END_SKIP_PROOF_ON *) admit.
  Qed.

  Ltac disc_AtomicMsgOutsInv oidx :=
    match goal with
    | [Ha: AtomicMsgOutsInv _ ?eouts _, Hin: In _ ?eouts |- _] =>
      red in Ha; rewrite Forall_forall in Ha; specialize (Ha _ Hin oidx);
      simpl in Ha; dest
    end.

  Ltac disc_MsgPred :=
    match goal with
    | [Hp: RsMPred _ (_, ?rmsg) _ _,
           Ht: msg_type ?rmsg = _,
               Hi: msg_id ?rmsg = msiRsM |- _] =>
      specialize (Hp eq_refl Ht Hi)
    | [Hp: DownRsSPred _ (_, ?rmsg) _ _,
           Ht: msg_type ?rmsg = _,
               Hi: msg_id ?rmsg = msiDownRsS |- _] =>
      specialize (Hp eq_refl Ht Hi)
    | [Hp: DownRsISPred _ (_, ?rmsg) _ _,
           Ht: msg_type ?rmsg = _,
               Hi: msg_id ?rmsg = msiDownRsIS |- _] =>
      specialize (Hp eq_refl Ht Hi)
    | [Hp: DownRsIMPred _ (_, ?rmsg) _ _,
           Ht: msg_type ?rmsg = _,
               Hi: msg_id ?rmsg = msiDownRsIM |- _] =>
      specialize (Hp eq_refl Ht Hi)
    | [Hp: InvRqPred _ (_, ?rmsg) _ _,
           Ht: msg_type ?rmsg = _,
               Hi: msg_id ?rmsg = msiInvRq |- _] =>
      specialize (Hp eq_refl Ht Hi)
    | [Hp: InvWRqPred _ (_, ?rmsg) _ _,
           Ht: msg_type ?rmsg = _,
               Hi: msg_id ?rmsg = msiInvWRq |- _] =>
      specialize (Hp eq_refl Ht Hi)
    end;
    try match goal with
        | [Hp: _ <+- ?oss@[?oidx]; _, Ho: ?oss@[?oidx] = Some _ |- _] =>
          rewrite Ho in Hp; simpl in Hp
        end.

  Ltac solve_AtomicInv_rqDown_rqDowns :=
    match goal with
    | [Hr: Reachable _ _ ?st,
           Hs: steps _ _ ?st ?hst _,
               Ha: Atomic _ _ ?hst _ ?eouts,
                   H: FirstMPI _ (?midx, ?msg)
       |- context [enqMP ?nmidx ?nmsg (deqMP ?midx _)] ] =>
      do 2 red; simpl;
      apply Forall_app;
      [change midx with (idOf (midx, msg)) at 1;
       eapply atomic_rqDown_rqDowns_preserves_msg_out_preds
         with (rqDowns:= [(nmidx, nmsg)]);
       try exact Hr; eauto; [red; auto; fail|]
      |repeat constructor;
       try (red; simpl; intros; intuition discriminate)]

    | [Hr: Reachable _ _ ?st,
           Hs: steps _ _ ?st ?hst _,
               Ha: Atomic _ _ ?hst _ ?eouts,
                   H: FirstMPI _ (?midx, ?msg)
       |- context [enqMsgs _ (deqMP ?midx _)] ] =>
      do 2 red; simpl;
      apply Forall_app;
      [change midx with (idOf (midx, msg)) at 1;
       eapply atomic_rqDown_rqDowns_preserves_msg_out_preds;
       try exact Hr; eauto; [red; auto; fail|]
      |repeat constructor;
       try (red; simpl; intros; intuition discriminate)]
    end.

  Ltac solve_AtomicInv_rsDown :=
    match goal with
    | [Hr: Reachable _ _ ?st,
           Hs: steps step_m _ ?st ?hst _,
               Ha: Atomic _ _ ?hst _ ?eouts,
                   Hin: In (downTo ?roidx, _) ?eouts
       |- AtomicInv _ _ _ _ _ _] =>
      do 2 red; simpl;
      eapply atomic_rsDown_singleton in Ha;
      try exact Hr; eauto; [|red; eauto];
      subst; rewrite removeOnce_nil; simpl;
      repeat constructor; try (red; simpl; intros; intuition discriminate)
    end.

  Ltac solve_AtomicInv_rqDown_rsUp :=
    match goal with
    | [Hr: Reachable _ _ ?st,
           Hs: steps _ _ ?st ?hst _,
               Ha: Atomic _ _ ?hst _ ?eouts,
                   H: FirstMPI _ (?midx, ?msg) |- context [deqMP ?midx _] ] =>
      do 2 red; simpl;
      apply Forall_app;
      [change midx with (idOf (midx, msg)) at 1;
       eapply atomic_rqDown_rsUp_preserves_msg_out_preds;
       try exact Hr; eauto;
       red; auto
      |repeat constructor;
       try (red; simpl; intros; intuition discriminate)]
    end.

  Ltac solve_AtomicInv_rsUps_rsDown Hrsd :=
    erewrite Hrsd;
    [|apply in_or_app; right; left; reflexivity|red; eauto];
    do 2 red; simpl;
    repeat constructor;
    try (red; simpl; intros; intuition discriminate).

  Ltac solve_AtomicInv_rsUps_rsUp :=
    repeat
      match goal with
      | _ => assumption
      | |- _ = _ => reflexivity

      | [Hr: Reachable _ _ ?st,
             Hs: steps _ _ ?st ?hst _,
                 Ha: Atomic _ _ ?hst _ ?eouts,
                     H: FirstMPI _ (?midx, ?msg) |- context [deqMP ?midx _] ] =>
        do 2 red; simpl; apply Forall_app;
        [change midx with (idOf (midx, msg)) at 1;
         eapply atomic_rsUps_rsUp_preserves_msg_out_preds
           with (rsUps:= [(midx, msg)]);
         try exact Hr; eauto
        |repeat constructor;
         try (red; simpl; intros; intuition discriminate)]
      | [Hr: Reachable _ _ ?st,
             Hs: steps _ _ ?st ?hst _,
                 Ha: Atomic _ _ ?hst _ ?eouts,
                     H: Forall (FirstMPI _) ?rss |- _] =>
        do 2 red; simpl; apply Forall_app;
        [eapply atomic_rsUps_rsUp_preserves_msg_out_preds
           with (rsUps:= rss); try exact Hr; eauto
        |repeat constructor;
         try (red; simpl; intros; intuition discriminate)]

      (* Belows are for the single RsUp input *)
      | [H: In (li _ ?oidx) _ |- In _ (sys_objs _)] =>
        right; apply in_or_app; left; eassumption
      | |- SubList [_] _ => apply SubList_cons; [|apply SubList_nil]
      end.

  Ltac solve_AtomicInv_rqUp :=
    match goal with
    | [Hr: Reachable _ _ ?st,
           Hs: steps step_m _ ?st ?hst _,
               Ha: Atomic _ _ ?hst _ ?eouts,
                   Hin: In (rqUpFrom ?roidx, _) ?eouts
       |- AtomicInv _ _ _ _ _ _] =>
      do 2 red; simpl;
      eapply atomic_rqUp_singleton in Ha;
      try exact Hr; eauto; [|red; eauto];
      subst; rewrite removeOnce_nil; simpl;
      repeat constructor; try (red; simpl; intros; intuition discriminate)
    end.

  Ltac solve_DownRsSPred :=
    solve_msg_pred_base; mred;
    try (simpl; intuition solve_msi).

  Ltac disc_dir :=
    repeat
      match goal with
      | [H: context[getDir _ _] |- _] => progress simpl in H
      | [H: context[getDir _ (addSharer _ _)] |- _] =>
        rewrite getDir_addSharer_spec in H by solve_msi;
        destruct (idx_dec _ _) in H; try solve_msi

      | [H: context[getDir ?cidx (setDirS [?cidx])] |- _] =>
        rewrite getDir_setDirS_eq in H
      | [H: context[getDir ?cidx (setDirM ?cidx)] |- _] =>
        rewrite getDir_setDirM_eq in H
      | [Hn: ?oidx1 <> ?oidx2, H: context[getDir ?oidx1 (setDirM ?oidx2)] |- _] =>
        rewrite getDir_setDirM_neq in H by auto
      | [Hn: ?oidx2 <> ?oidx1, H: context[getDir ?oidx1 (setDirM ?oidx2)] |- _] =>
        rewrite getDir_setDirM_neq in H by auto
      end;
    try match goal with
        | [H: msiS <= getDir ?cidx ?dir |- _] =>
          pose proof (getDir_st_sound dir cidx ltac:(solve_msi))
        end.

  Ltac derive_child_st cidx :=
    match goal with
    | [Hosi: OstInds _ _ _,
             Hoin: In ?oidx (tl (c_li_indices _)),
                   Hp: parentIdxOf _ cidx = Some ?oidx |- _] =>
      let Hin := fresh "H" in
      pose proof (tree2Topo_li_child_li_l1 _ _ _ (tl_In _ _ Hoin) Hp) as Hin;
      let Ho := fresh "H" in
      pose proof (Hosi _ Hin) as Ho;
      let cost := fresh "cost" in
      let corq := fresh "corq" in
      simpl in Ho; destruct Ho as [[cost ?] [corq ?]]
    | [Hosi: OstInds _ _ _,
             Hoin: In ?oidx (c_li_indices _),
                   Hp: parentIdxOf _ cidx = Some ?oidx |- _] =>
      let Hin := fresh "H" in
      pose proof (tree2Topo_li_child_li_l1 _ _ _ Hoin Hp) as Hin;
      let Ho := fresh "H" in
      pose proof (Hosi _ Hin) as Ho;
      let cost := fresh "cost" in
      let corq := fresh "corq" in
      simpl in Ho; destruct Ho as [[cost ?] [corq ?]]
    end.

  Ltac disc_InvDirInv cidx :=
    match goal with
    | [Hi: InvDirInv _ _ _ _ _ _,
           Hoin: In ?oidx (tl (c_li_indices _)),
                 Hp: parentIdxOf _ cidx = Some ?oidx |- _] =>
      specialize (Hi (tl_In _ _ Hoin) _ Hp); dest
    | [Hi: InvDirInv _ _ _ _ _ _,
           Hoin: In ?oidx (c_li_indices _),
                 Hp: parentIdxOf _ cidx = Some ?oidx |- _] =>
      specialize (Hi Hoin _ Hp); dest
    end.

  Local Hint Extern 0 (NoDup (idsOf _)) =>
  match goal with
  | [H: ValidMsgsIn _ _ |- _] => apply H
  end.

  Lemma msi_InvExcl_InvTrs_mem:
    forall ist1,
      Reachable (steps step_m) impl ist1 ->
      forall inits,
        SubList (idsOf inits) (sys_merqs impl) ->
        forall ins hst outs eouts oidx ridx rins routs,
          Atomic inits ins hst outs eouts ->
          rins <> nil ->
          SubList rins eouts ->
          forall (Hrsd: forall (oidx : IdxT) (rsDown : Id Msg),
                     In rsDown (removeL (id_dec msg_dec) eouts rins ++ routs) ->
                     RsDownMsgTo topo oidx rsDown ->
                     removeL (id_dec msg_dec) eouts rins ++ routs = [rsDown])
                 st2 ist2,
            InvExcl topo cifc st2 ->
            AtomicInv InvExclMsgOutPred inits ist1 hst eouts st2 ->
            steps step_m impl ist1 hst st2 ->
            step_m impl st2 (RlblInt oidx ridx rins routs) ist2 ->
            forall (Hr1: Reachable (steps step_m) impl st2)
                   (Hr2: Reachable (steps step_m) impl ist2)
                   (Hoin: rootOf (fst (tree2Topo tr 0)) = oidx),
              AtomicInv InvExclMsgOutPred inits ist1 (RlblInt oidx ridx rins routs :: hst)
                        (removeL (id_dec msg_dec) eouts rins ++ routs) ist2 /\
              InvExcl topo cifc ist2.
  Proof. (* SKIP_PROOF_ON
    intros.
    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    pose proof (footprints_ok
                  (msi_GoodORqsInit Htr)
                  (msi_GoodRqRsSys Htr) Hr1) as Hftinv.
    pose proof (msi_InObjInds Hr1) as Hioi1.
    pose proof (msi_InObjInds Hr2) as Hioi2.
    pose proof (msi_OstInds Hr1) as Hosi.
    pose proof (msi_MsgConflictsInv
                  (@msi_RootChnInv_ok _ Htr) Hr1) as Hpmcf.
    pose proof (@MsiUpLockInv_ok _ Htr _ Hr1) as Hulinv.
    pose proof (@MsiDownLockInv_ok _ Htr _ Hr1) as Hdlinv.
    pose proof (@msi_InvWBDir_ok _ Htr _ Hr1) as Hidir.
    pose proof (@msi_InvWB_ok _ Htr _ Hr1) as Hwb.

    inv_step.

    simpl in H12; destruct H12; [subst|apply in_app_or in H7; destruct H7].
    2: {
      exfalso.
      apply in_map with (f:= obj_idx) in H7; rewrite <-H14 in H7.
      rewrite map_map in H7; simpl in H7; rewrite map_id in H7.
      eapply tree2Topo_root_not_in_tl_li; eauto.
    }
    2: {
      exfalso.
      apply in_map with (f:= obj_idx) in H7; rewrite <-H14 in H7.
      rewrite map_map in H7; simpl in H7; rewrite map_id in H7.
      eapply tree2Topo_root_not_in_l1; eauto.
    }

    (*! Cases for the main memory *)

    (** Abstract the root. *)
    assert (In (rootOf (fst (tree2Topo tr 0)))
               (c_li_indices (snd (tree2Topo tr 0)))) as Hin.
    { rewrite c_li_indices_head_rootOf by assumption.
      left; reflexivity.
    }

    remember (rootOf (fst (tree2Topo tr 0))) as oidx; clear Heqoidx.
    clear H14.

    (** Do case analysis per a rule. *)
    apply concat_In in H13; destruct H13 as [crls [? ?]].
    apply in_map_iff in H7; destruct H7 as [cidx [? ?]]; subst.

    (** Derive that the child has the parent. *)
    assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
      by (apply subtreeChildrenIndsOf_parentIdxOf; auto).
    derive_child_chns cidx.

    dest_in.

    { (* [liGetSImmM] *)
      disc_rule_conds_ex.
      derive_NoRsI_by_no_uplock oidx msgs.

      split.
      { solve_AtomicInv_rqUp. }
      { case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { case_InvObjOwned.
            { solve_by_topo_false. }
            { disc_ObjsInvalid_by oidx0.
              case_ObjInvalid_with cidx; [solve_by_topo_false|].
              case_ObjInvalid; [solve_ObjInvalid0|].
              solve_ObjInvRs.
            }
            { solve_MsgsP. }
          }
          { split_InvDirInv.
            { assert (ObjExcl0 oidx os msgs)
                by (split; [simpl; solve_msi|assumption]).
              specialize (H4 H32); dest.
              simpl in H31; case_idx_eq cidx0 cidx; [disc_dir; discriminate|].
              solve_ObjsInvalid_trivial.
              eapply ObjsInvalid_impl; [eassumption|].
              simpl; intros; intro; subst; solve_by_topo_false.
            }
            { simpl in H31.
              pose proof (getDir_setDirS_sound cidx0 [cidx]).
              solve_msi.
            }
          }
        }

        { disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            solve_by_ObjsInvalid_status_false oidx.
          }
          { case_InvObjOwned.
            { solve_by_ObjsInvalid_status_false oidx. }
            { derive_not_InvalidObj_not_in oidx.
              disc_ObjsInvalid_by oidx0.
              case_ObjInvalid_with cidx; [solve_by_topo_false|].
              case_ObjInvalid; [solve_ObjInvalid0|].
              solve_ObjInvRs.
            }
            { case_idx_eq eidx cidx.
              { apply parent_not_in_subtree in H7; auto.
                solve_by_ObjsInvalid_status_false oidx.
              }
              { solve_MsgsP. }
            }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx0.
              { solve_by_ObjsInvalid_status_false oidx. }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx0.
              { solve_ObjsInvalid_trivial. }
              { solve_by_ObjsInvalid_status_false oidx. }
            }
          }
        }
      }
    }

    { (* [liGetMImm] *)
      disc_rule_conds_ex.
      derive_NoRsI_by_no_uplock oidx msgs.

      rename H23 into Hprec. (* the precondition about status and ownership bit *)
      assert (ObjsInvalid
                (fun idx => ~ In idx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx))
                (oss +[oidx <- (fst os, (false, (msiI, (setDirM cidx, snd (snd (snd (snd os)))))))])
                msgs) as Hoi.
      { destruct Hprec; dest.
        { disc_InvExcl oidx.
          assert (ObjExcl0 oidx os msgs)
            by (split; [simpl; solve_msi|assumption]).
          specialize (H4 H27); dest.
          apply ObjsInvalid_rsM_generated; auto; discriminate.
        }
        { disc_InvExcl oidx.
          eapply ObjsInvalid_out_composed; eauto.
          { solve_ObjsInvalid_trivial.
            apply H28; red; auto.
          }
          { mred. }
          { left; repeat split; [simpl; solve_msi|discriminate|apply H28; red; auto]. }
          { intros.
            solve_ObjsInvalid_trivial.
            disc_InvDirInv rcidx.
            apply H29.
            eapply getDir_LastSharer_neq; try eassumption.
            eapply getDir_LastSharer_eq; eassumption.
          }
        }
      }

      split.
      { solve_AtomicInv_rqUp.
        disc_InvExcl oidx.
        solve_msg_pred_base.
        solve_ObjsInvalid_trivial.
      }

      { case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { split_InvDirInv.
            { simpl in H29; case_idx_eq cidx0 cidx; [disc_dir; discriminate|].
              solve_ObjsInvalid_trivial.
              destruct Hprec; dest.
              { assert (ObjExcl0 oidx os msgs)
                  by (split; [simpl; solve_msi|assumption]).
                specialize (H4 H31); dest.
                eapply ObjsInvalid_impl; [apply H4|].
                simpl; intros; intro; subst; solve_by_topo_false.
              }
              { apply H20.
                eapply getDir_LastSharer_neq; try eassumption.
                eapply getDir_LastSharer_eq; eassumption.
              }
            }
            { simpl in H29; case_idx_eq cidx0 cidx; [|disc_dir; solve_msi].
              solve_ObjsInvalid_trivial.
            }
          }
        }

        { clear Hoi.
          disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            solve_by_ObjsInvalid_status_false oidx.
          }
          { case_InvObjOwned.
            { solve_by_ObjsInvalid_status_false oidx. }
            { derive_not_InvalidObj_not_in oidx.
              disc_ObjsInvalid_by oidx0.
              case_ObjInvalid_with cidx; [solve_by_topo_false|].
              case_ObjInvalid; [solve_ObjInvalid0|].
              solve_ObjInvRs.
            }
            { case_idx_eq eidx cidx.
              { apply parent_not_in_subtree in H7; auto.
                solve_by_ObjsInvalid_status_false oidx.
              }
              { solve_MsgsP. }
            }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx0.
              { solve_by_ObjsInvalid_status_false oidx. }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx0.
              { solve_ObjsInvalid_trivial. }
              { solve_by_ObjsInvalid_status_false oidx. }
            }
          }
        }
      }
    }

    { (* [liInvImmWBM] *)
      disc_rule_conds_ex.
      derive_child_st cidx.
      derive_NoRsI_by_rqUp cidx msgs.
      rename H20 into Hrsi.

      assert (ObjsInvalid
                (fun idx => In idx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx))
                (oss +[oidx <- (msg_value rmsg, (true, (msiM, (setDirI, snd (snd (snd (snd os)))))))])
                (enqMP (downTo cidx) {| msg_id := msiInvRs;
                                        msg_type := MRs;
                                        msg_addr := msg_addr rmsg;
                                        msg_value := 0 |}
                       (deqMP (rqUpFrom cidx) msgs))) as Hci.
      { disc_AtomicMsgOutsInv cidx.
        disc_MsgPred.
        eapply InvExcl_inv_ObjsInvalid; eauto.
      }

      assert (ObjsInvalid
                (fun idx => ~ In idx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx))
                oss msgs) as Hcci.
      { disc_InvExcl oidx.
        disc_InvDirInv cidx.
        apply H29.
        simpl; solve_msi.
      }

      assert (ObjsInvalid
                (fun idx => oidx <> idx)
                (oss +[oidx <- (msg_value rmsg, (true, (msiM, (setDirI, snd (snd (snd (snd os)))))))])
                (enqMP (downTo cidx) {| msg_id := msiInvRs;
                                        msg_type := MRs;
                                        msg_addr := msg_addr rmsg;
                                        msg_value := 0 |}
                       (deqMP (rqUpFrom cidx) msgs))) as Hoi.
      { eapply ObjsInvalid_invRs_composed.
        { solve_ObjsInvalid_trivial.
          eapply ObjsInvalid_impl; [apply Hcci|].
          simpl; intros.
          intro Hx; elim H20.
          eapply subtreeIndsOf_child_SubList; eauto.
        }
        { apply ObjsInvalid_child_forall; intros rcidx ?.
          case_idx_eq rcidx cidx; [assumption|].
          solve_ObjsInvalid_trivial.
          disc_InvExcl oidx.
          disc_InvDirInv rcidx.
          apply H29.
          apply getDir_M_imp in H23; dest; subst.
          eapply getDir_excl_neq; eauto.
        }
      }

      split; [solve_AtomicInv_rqUp|].
      case_InvExcl_me_others.
      { disc_InvExcl_this.
        { disc_InvObjExcl0; split; [apply Hoi|].
          disc_MsgConflictsInv oidx.
          solve_MsgsP.
          eapply ObjInvalid_NoCohMsgs; eauto.
          eapply ObjsInvalid_ObjInvalid; try exact Hcci; eauto.
          simpl; intro; solve_by_topo_false.
        }
        { disc_InvDirInv cidx.
          simpl in *; rewrite H23 in H28.
          specialize (H29 ltac:(solve_msi)).
          disc_InvObjOwned; split.
          { solve_ObjsInvalid_trivial.
            eapply ObjsInvalid_impl; [apply H29|].
            simpl; intros.
            intro Hx; elim H32.
            eapply subtreeIndsOf_child_SubList with (cidx:= cidx); eauto.
          }
          { disc_MsgConflictsInv oidx.
            apply parent_not_in_subtree in H7; auto.
            specialize (H29 _ H7); rewrite H15 in H29; simpl in H29.
            solve_MsgsP.
            eapply ObjInvalid_NoCohMsgs; eauto.
          }
        }
        { split_InvDirInv; [|exfalso; rewrite getDir_setDirI in H32; solve_msi].
          case_idx_eq cidx0 cidx.
          { apply Hci. }
          { solve_ObjsInvalid_trivial.
            apply H28.
            apply getDir_M_imp in H23; dest; subst.
            eapply getDir_excl_neq;
              [reflexivity|simpl; solve_msi|assumption].
          }
        }
      }

      { assert (msiS <= cost#[status]).
        { (** TODO: bring [disc_InvWB] to here? *)
          move Hwb at bottom.
          specialize (Hwb _ _ H7); simpl in Hwb.
          disc_rule_conds_ex.
          apply Hwb.
          { apply getDir_M_imp in H23; dest.
            repeat split; try assumption.
          }
          { eexists (_, _); split; [apply FirstMP_InMP; eassumption|].
            unfold sigOf; simpl; congruence.
          }
        }

        disc_InvExcl_others.
        { case_idx_eq eidx cidx.
          { red; intros [? ?]; exfalso.
            apply NoRsI_MsgExistsSig_InvRs_false in H32; auto.
            eexists (_, _); split.
            { apply InMP_or_enqMP; left; simpl; auto. }
            { reflexivity. }
          }
          { disc_InvObjExcl0.
            destruct H31.
            clear Hci Hcci.
            exfalso; eapply ObjsInvalid_obj_status_false with (oidx := eidx);
              eauto; simpl in *; auto.
            { solve_MsgsP. }
            { mred. }
            { solve_msi. }
          }
        }

        { case_in_subtree oidx eidx.
          { disc_InvObjOwned.
            split; [solve_ObjsInvalid_trivial|solve_MsgsP].
          }
          { case_in_subtree cidx eidx.
            { eapply inside_child_outside_parent_case in i; eauto; subst.
              red; intros [? ?]; exfalso.
              apply NoRsI_MsgExistsSig_InvRs_false in H32; auto.
              eexists (_, _); split.
              { apply InMP_or_enqMP; left; simpl; auto. }
              { reflexivity. }
            }
            { disc_InvObjOwned.
              clear Hci Hcci Hoi; solve_by_ObjsInvalid_status_false cidx.
            }
          }
        }

        { split_InvDirInv_apply.
          { case_in_subtree oidx cidx0.
            { clear Hci Hcci Hoi.
              eapply inside_child_in in i; eauto.
              solve_by_ObjsInvalid_status_false cidx.
            }
            { solve_ObjsInvalid_trivial. }
          }
          { case_in_subtree oidx cidx0.
            { solve_ObjsInvalid_trivial. }
            { eapply outside_child_in in n0; eauto.
              destruct n0; subst; [disc_rule_conds_ex|].
              clear Hci Hcci Hoi.
              solve_by_ObjsInvalid_status_false cidx.
            }
          }
        }
      }
    }

    END_SKIP_PROOF_ON *) admit.
  Qed.

  Lemma msi_InvExcl_InvTrs_li:
    forall ist1,
      Reachable (steps step_m) impl ist1 ->
      forall inits,
        SubList (idsOf inits) (sys_merqs impl) ->
        forall ins hst outs eouts oidx ridx rins routs,
          Atomic inits ins hst outs eouts ->
          rins <> nil ->
          SubList rins eouts ->
          forall (Hrsd: forall (oidx : IdxT) (rsDown : Id Msg),
                     In rsDown (removeL (id_dec msg_dec) eouts rins ++ routs) ->
                     RsDownMsgTo topo oidx rsDown ->
                     removeL (id_dec msg_dec) eouts rins ++ routs = [rsDown])
                 st2 ist2,
            InvExcl topo cifc st2 ->
            AtomicInv InvExclMsgOutPred inits ist1 hst eouts st2 ->
            steps step_m impl ist1 hst st2 ->
            step_m impl st2 (RlblInt oidx ridx rins routs) ist2 ->
            forall (Hr1: Reachable (steps step_m) impl st2)
                   (Hr2: Reachable (steps step_m) impl ist2)
                   (Hoin: In oidx (map obj_idx (map (li tr) (tl (c_li_indices (snd (tree2Topo tr 0))))))),
              AtomicInv InvExclMsgOutPred inits ist1 (RlblInt oidx ridx rins routs :: hst)
                        (removeL (id_dec msg_dec) eouts rins ++ routs) ist2 /\
              InvExcl topo cifc ist2.
  Proof. (* SKIP_PROOF_ON
    intros.
    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    pose proof (footprints_ok
                  (msi_GoodORqsInit Htr)
                  (msi_GoodRqRsSys Htr) Hr1) as Hftinv.
    pose proof (msi_InObjInds Hr1) as Hioi1.
    pose proof (msi_InObjInds Hr2) as Hioi2.
    pose proof (msi_OstInds Hr1) as Hosi.
    pose proof (msi_MsgConflictsInv
                  (@msi_RootChnInv_ok _ Htr) Hr1) as Hpmcf.
    pose proof (msi_MsgConflictsInv
                  (@msi_RootChnInv_ok _ Htr) Hr2) as Hnmcf.
    phide Hnmcf; rename H8 into Hnmcf.
    pose proof (@MsiUpLockInv_ok _ Htr _ Hr1) as Hulinv.
    pose proof (@MsiDownLockInv_ok _ Htr _ Hr1) as Hdlinv.
    pose proof (@msi_InvWBDir_ok _ Htr _ Hr1) as Hidir.
    pose proof (@msi_InvWB_ok _ Htr _ Hr1) as Hwb.

    inv_step.

    simpl in H12; destruct H12; [subst|apply in_app_or in H7; destruct H7].
    1: {
      exfalso; simpl in Hoin.
      rewrite map_map in Hoin; simpl in Hoin; rewrite map_id in Hoin.
      eapply tree2Topo_root_not_in_tl_li; eauto.
    }
    2: {
      exfalso; simpl in Hoin.
      apply in_map_iff in H7; destruct H7 as [oidx [? ?]]; subst.
      rewrite map_map in Hoin; simpl in Hoin; rewrite map_id in Hoin.
      pose proof (tree2Topo_WfCIfc tr 0) as [? _].
      apply (DisjList_NoDup idx_dec) in H7.
      eapply DisjList_In_1; eauto.
      apply tl_In; assumption.
    }

    (*! Cases for Li caches *)
    pose proof H7 as Hobj.
    apply in_map_iff in H7; destruct H7 as [oidx [? ?]]; subst; simpl in *.

    pose proof (c_li_indices_tail_has_parent Htr _ _ H8).
    destruct H7 as [pidx [? ?]].
    pose proof (Htn _ _ H9); dest.

    (** Do case analysis per a rule. *)
    apply in_app_or in H13; destruct H13.

    1: { (** Rules per a child *)
      apply concat_In in H13; destruct H13 as [crls [? ?]].
      apply in_map_iff in H13; destruct H13 as [cidx [? ?]]; subst.

      (** Derive that the child has the parent. *)
      assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
        by (apply subtreeChildrenIndsOf_parentIdxOf; auto).
      derive_child_chns cidx.

      dest_in.

      { (* [liGetSImmS] *)
        disc_rule_conds_ex.
        derive_NoRsI_by_no_uplock oidx msgs.

        split; [solve_AtomicInv_rqUp|].
        case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { case_InvObjOwned.
            { solve_by_topo_false. }
            { disc_ObjsInvalid_by oidx0.
              case_ObjInvalid_with cidx; [solve_by_topo_false|].
              case_ObjInvalid; [solve_ObjInvalid0|].
              solve_ObjInvRs.
            }
            { solve_MsgsP. }
          }
          { split_InvDirInv.
            { simpl in H37; rewrite getDir_addSharer_spec in H37 by solve_msi.
              find_if_inside; subst; [discriminate|].
              specialize (H27 H37).
              solve_ObjsInvalid_trivial.
            }
            { simpl in H37; rewrite getDir_addSharer_spec in H37 by solve_msi.
              find_if_inside; subst; [solve_msi|].
              pose proof (getDir_st_sound (fst (snd (snd (snd os)))) cidx0 ltac:(solve_msi)).
              solve_msi.
            }
          }
        }

        { disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            solve_by_ObjsInvalid_status_false oidx.
          }
          { case_InvObjOwned.
            { solve_by_ObjsInvalid_status_false oidx. }
            { derive_not_InvalidObj_not_in oidx.
              disc_ObjsInvalid_by oidx0.
              case_ObjInvalid_with cidx; [solve_by_topo_false|].
              case_ObjInvalid; [solve_ObjInvalid0|].
              solve_ObjInvRs.
            }
            { case_idx_eq eidx cidx.
              { apply parent_not_in_subtree in H13; auto.
                solve_by_ObjsInvalid_status_false oidx.
              }
              { solve_MsgsP. }
            }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx0.
              { solve_by_ObjsInvalid_status_false oidx. }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx0.
              { solve_ObjsInvalid_trivial. }
              { solve_by_ObjsInvalid_status_false oidx. }
            }
          }
        }
      }

      { (* [liGetSImmM] *)
        disc_rule_conds_ex.
        derive_NoRsI_by_no_uplock oidx msgs.

        split.
        { solve_AtomicInv_rqUp. }
        { case_InvExcl_me_others.
          { disc_InvExcl_this.
            { solve_InvObjExcl0_by_ObjExcl0_false. }
            { case_InvObjOwned.
              { solve_by_topo_false. }
              { disc_ObjsInvalid_by oidx0.
                case_ObjInvalid_with cidx; [solve_by_topo_false|].
                case_ObjInvalid; [solve_ObjInvalid0|].
                solve_ObjInvRs.
              }
              { solve_MsgsP. }
            }
            { split_InvDirInv.
              { assert (ObjExcl0 oidx os msgs)
                  by (split; [simpl; solve_msi|assumption]).
                specialize (H4 H38); dest.
                simpl in H37; case_idx_eq cidx0 cidx; [disc_dir; discriminate|].
                solve_ObjsInvalid_trivial.
                eapply ObjsInvalid_impl; [eassumption|].
                simpl; intros; intro; subst; solve_by_topo_false.
              }
              { simpl in H37.
                pose proof (getDir_setDirS_sound cidx0 [cidx]).
                solve_msi.
              }
            }
          }

          { disc_InvExcl_others.
            { disc_InvObjExcl0_apply.
              solve_by_ObjsInvalid_status_false oidx.
            }
            { case_InvObjOwned.
              { solve_by_ObjsInvalid_status_false oidx. }
              { derive_not_InvalidObj_not_in oidx.
                disc_ObjsInvalid_by oidx0.
                case_ObjInvalid_with cidx; [solve_by_topo_false|].
                case_ObjInvalid; [solve_ObjInvalid0|].
                solve_ObjInvRs.
              }
              { case_idx_eq eidx cidx.
                { apply parent_not_in_subtree in H13; auto.
                  solve_by_ObjsInvalid_status_false oidx.
                }
                { solve_MsgsP. }
              }
            }
            { split_InvDirInv_apply.
              { case_in_subtree oidx cidx0.
                { solve_by_ObjsInvalid_status_false oidx. }
                { solve_ObjsInvalid_trivial. }
              }
              { case_in_subtree oidx cidx0.
                { solve_ObjsInvalid_trivial. }
                { solve_by_ObjsInvalid_status_false oidx. }
              }
            }
          }
        }
      }

      { (* [liGetSRqUpUp] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_rqUp.
          all: try (red; simpl; intros; rewrite H19 in H20; discriminate).
        }
        { solve_InvExcl_trivial. }
      }

      { (* [liGetSRqUpDownM] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_rqUp. }
        { solve_InvExcl_trivial. }
      }

      { (* [liGetMImm] *)
        disc_rule_conds_ex.
        derive_NoRsI_by_no_uplock oidx msgs.

        rename H30 into Hprec. (* the precondition about status and ownership bit *)
        assert (ObjsInvalid
                  (fun idx => ~ In idx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx))
                  (oss +[oidx <- (fst os, (false, (msiI, (setDirM cidx, snd (snd (snd (snd os)))))))])
                  msgs) as Hoi.
        { destruct Hprec; dest.
          { disc_InvExcl oidx.
            assert (ObjExcl0 oidx os msgs)
              by (split; [simpl; solve_msi|assumption]).
            specialize (H4 H33); dest.
            apply ObjsInvalid_rsM_generated; auto; discriminate.
          }
          { disc_InvExcl oidx.
            eapply ObjsInvalid_out_composed; eauto.
            { solve_ObjsInvalid_trivial.
              apply H34; red; auto.
            }
            { mred. }
            { left; repeat split; [simpl; solve_msi|discriminate|apply H34; red; auto]. }
            { intros.
              solve_ObjsInvalid_trivial.
              disc_InvDirInv rcidx.
              apply H35.
              eapply getDir_LastSharer_neq; try eassumption.
              eapply getDir_LastSharer_eq; eassumption.
            }
          }
        }

        split.
        { solve_AtomicInv_rqUp.
          disc_InvExcl oidx.
          solve_msg_pred_base.
          solve_ObjsInvalid_trivial.
        }

        { case_InvExcl_me_others.
          { disc_InvExcl_this.
            { solve_InvObjExcl0_by_ObjExcl0_false. }
            { solve_InvObjOwned_by_false. }
            { split_InvDirInv.
              { simpl in H35;case_idx_eq cidx0 cidx; [disc_dir; discriminate|].
                solve_ObjsInvalid_trivial.
                destruct Hprec; dest.
                { assert (ObjExcl0 oidx os msgs)
                    by (split; [simpl; solve_msi|assumption]).
                  specialize (H4 H37); dest.
                  eapply ObjsInvalid_impl; [apply H4|].
                  simpl; intros; intro; subst; solve_by_topo_false.
                }
                { apply H27.
                  eapply getDir_LastSharer_neq; try eassumption.
                  eapply getDir_LastSharer_eq; eassumption.
                }
              }
              { simpl in H35; case_idx_eq cidx0 cidx; [|disc_dir; solve_msi].
                solve_ObjsInvalid_trivial.
              }
            }
          }

          { clear Hoi.
            disc_InvExcl_others.
            { disc_InvObjExcl0_apply.
              destruct Hprec; dest; solve_by_ObjsInvalid_status_false oidx.
            }
            { case_InvObjOwned.
              { destruct Hprec; dest; solve_by_ObjsInvalid_status_false oidx. }
              { destruct Hprec; dest.
                all: derive_not_InvalidObj_not_in oidx;
                  disc_ObjsInvalid_by oidx0;
                  case_ObjInvalid_with cidx; [solve_by_topo_false|];
                    case_ObjInvalid; [solve_ObjInvalid0|];
                      solve_ObjInvRs.
              }
              { case_idx_eq eidx cidx.
                { apply parent_not_in_subtree in H13; auto.
                  destruct Hprec; dest; solve_by_ObjsInvalid_status_false oidx.
                }
                { solve_MsgsP. }
              }
            }
            { split_InvDirInv_apply.
              { case_in_subtree oidx cidx0.
                { destruct Hprec; dest; solve_by_ObjsInvalid_status_false oidx. }
                { solve_ObjsInvalid_trivial. }
              }
              { case_in_subtree oidx cidx0.
                { destruct Hprec; dest; solve_ObjsInvalid_trivial. }
                { solve_by_ObjsInvalid_status_false oidx. }
              }
            }
          }
        }
      }

      { (* [liGetMRqUpUp] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_rqUp.
          all: try (red; simpl; intros; rewrite H19 in H20; discriminate).
        }
        { solve_InvExcl_trivial. }
      }

      { (* [liGetMRqUpDownM] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_rqUp. }
        { solve_InvExcl_trivial. }
      }

      { (* [liGetMRqUpDownS] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_rqUp.
          apply Forall_forall; intros.
          apply in_map_iff in H1; destruct H1 as [midx [? ?]]; subst.
          repeat constructor; try (red; simpl; intros; intuition discriminate).
        }
        { solve_InvExcl_trivial. }
      }

      { (* [liInvImmI] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_rqUp. }
        { solve_InvExcl_trivial. }
      }

      { (* [liInvImmS00] *)
        disc_rule_conds_ex.
        derive_child_st cidx.
        split; [solve_AtomicInv_rqUp|].
        pose proof H4 as Hi; phide Hi; rename H35 into Hi.

        case_InvExcl_me_others.
        { disc_InvExcl_this.
          { disc_InvObjExcl0_apply.
            split; [solve_ObjsInvalid_trivial|solve_MsgsP].
          }
          { disc_InvObjOwned.
            split; [solve_ObjsInvalid_trivial|solve_MsgsP].
          }
          { split_InvDirInv; [|exfalso; rewrite getDir_setDirI in H40; solve_msi].
            case_idx_eq cidx0 cidx.
            { disc_AtomicMsgOutsInv cidx.
              disc_MsgPred.
              eapply InvExcl_inv_ObjsInvalid; eauto.
              preveal Hi; assumption.
            }
            { solve_ObjsInvalid_trivial.
              apply H36.
              eapply getDir_LastSharer_neq; eauto.
            }
          }
        }

        { disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            split; [|solve_MsgsP].
            eapply ObjsInvalid_state_transition_sound; eauto; [|simpl; solve_msi].
            solve_ObjsInvalid_trivial.
          }
          { disc_InvObjOwned.
            split; [|solve_MsgsP].
            eapply ObjsInvalid_state_transition_sound; eauto; [|simpl; solve_msi].
            solve_ObjsInvalid_trivial.
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx0.
              { eapply ObjsInvalid_state_transition_sound; eauto; [|simpl; solve_msi].
                solve_ObjsInvalid_trivial.
              }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx0.
              { solve_ObjsInvalid_trivial. }
              { eapply ObjsInvalid_state_transition_sound; eauto; [|simpl; solve_msi].
                solve_ObjsInvalid_trivial.
              }
            }
          }
        }
      }

      { (* [liInvImmS01] *)
        disc_rule_conds_ex.
        derive_child_st cidx.
        derive_NoRsI_by_rqUp cidx msgs.
        rename H36 into Hcrsi.

        (** 1) The requestor subtree satisfies [ObjsInvalid] *)
        assert (ObjsInvalid
                  (fun idx => In idx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx))
                  (oss +[oidx <- (fst os, (fst (snd os), (msiM, (setDirI, snd (snd (snd (snd os)))))))])
                  (enqMP (downTo cidx) {| msg_id := msiInvRs;
                                          msg_type := MRs;
                                          msg_addr := msg_addr rmsg;
                                          msg_value := 0 |}
                         (deqMP (rqUpFrom cidx) msgs))) as Hci.
        { disc_AtomicMsgOutsInv cidx.
          disc_MsgPred.
          eapply InvExcl_inv_ObjsInvalid; eauto.
        }

        (** 2-1) Each child (except the requestor) has the directory status I *)
        assert (forall rcidx,
                   parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx ->
                   rcidx <> cidx ->
                   getDir rcidx os#[dir] = msiI) as Hcs.
        { intros; eapply getDir_LastSharer_neq; eassumption. }

        (** 2-2) Each child subtree (except the requestor) satisfies [ObjsInvalid] *)
        assert (forall rcidx,
                   parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx ->
                   rcidx <> cidx ->
                   forall nost rsTo,
                     ObjsInvalid
                       (fun idx =>
                          In idx (subtreeIndsOf (fst (tree2Topo tr 0)) rcidx))
                       (oss +[oidx <- nost])
                       (enqMP (downTo cidx) rsTo (deqMP (rqUpFrom cidx) msgs))) as Hcsi.
        { intros.
          specialize (Hcs _ H36 H37).
          disc_InvExcl oidx.
          specialize (H39 (tl_In _ _ H8)).
          move H39 at bottom.
          specialize (H39 _ H36); destruct H39 as [? _].
          specialize (H39 Hcs).
          solve_ObjsInvalid_trivial.
        }

        assert (NoRsI oidx msgs) as Hrsi.
        { move Hidir at bottom.
          specialize (Hidir oidx); simpl in Hidir.
          rewrite H15 in Hidir; simpl in Hidir.
          eapply not_MsgExistsSig_MsgsNotExist; intros;
            inv H36; [|dest_in].
          specialize (Hidir (or_intror (or_intror H37))).
          disc_getDir; simpl in *; solve_msi.
        }

        (** 2-2) ObjsInvalid, outside [oidx] *)
        assert (forall nost rsTo,
                   ObjsInvalid
                     (fun idx => ~ In idx (subtreeIndsOf (fst (tree2Topo tr 0)) oidx))
                     (oss +[oidx <- nost])
                     (enqMP (downTo cidx) rsTo (deqMP (rqUpFrom cidx) msgs))) as Hoo.
        { intros.
          solve_ObjsInvalid_trivial.
          disc_InvExcl oidx.
          apply H36. (* InvObjOwned *)
          red; auto.
        }

        (** 3) All [ObjsInvalid], except [oidx] *)
        assert (ObjsInvalid
                  (fun oidx0 : IdxT => oidx <> oidx0)
                  (oss +[oidx <- (fst os, (fst (snd os), (msiM, (setDirI, snd (snd (snd (snd os)))))))])
                  (enqMP (downTo cidx) {| msg_id := msiInvRs;
                                          msg_type := MRs;
                                          msg_addr := msg_addr rmsg;
                                          msg_value := 0 |}
                         (deqMP (rqUpFrom cidx) msgs))) as Hoi.
        { eapply ObjsInvalid_invRs_composed.
          { apply Hoo. }
          { eapply ObjsInvalid_downRsIM_composed; [mred|].
            intros; case_idx_eq rcidx cidx; auto.
          }
        }

        split; [solve_AtomicInv_rqUp|].
        pose proof H4 as Hi; phide Hi; rename H36 into Hi.

        case_InvExcl_me_others.
        { disc_InvExcl_this.
          { disc_InvObjExcl0.
            split; [apply Hoi|].
            solve_MsgsP.
            apply H36. (* InvObjOwned *)
            red; auto.
          }
          { disc_InvObjOwned.
            split; [solve_ObjsInvalid_trivial|solve_MsgsP].
          }
          { split_InvDirInv; [|exfalso; rewrite getDir_setDirI in H41; solve_msi].
            case_idx_eq cidx0 cidx.
            { disc_AtomicMsgOutsInv cidx.
              disc_MsgPred.
              eapply InvExcl_inv_ObjsInvalid; eauto.
              preveal Hi; assumption.
            }
            { solve_ObjsInvalid_trivial.
              apply H37.
              eapply getDir_LastSharer_neq; eauto.
            }
          }
        }

        { disc_InvExcl_others.
          { case_idx_eq eidx cidx.
            { red; intros [? ?]; exfalso.
              apply NoRsI_MsgExistsSig_InvRs_false in H40; auto.
              eexists (_, _); split.
              { apply InMP_or_enqMP; left; simpl; auto. }
              { reflexivity. }
            }
            { disc_InvObjExcl0_apply.
              destruct H39.
              clear Hci.
              exfalso; eapply ObjsInvalid_obj_status_false with (oidx := eidx);
                eauto; simpl in *; auto.
              { solve_MsgsP. }
              { mred. }
              { solve_msi. }
            }
          }

          { case_in_subtree oidx eidx.
            { disc_InvObjOwned.
              split; [solve_ObjsInvalid_trivial|solve_MsgsP].
            }
            { case_in_subtree cidx eidx.
              { eapply inside_child_outside_parent_case in i; eauto; subst.
                red; intros [? ?]; exfalso.
                apply NoRsI_MsgExistsSig_InvRs_false in H40; auto.
                eexists (_, _); split.
                { apply InMP_or_enqMP; left; simpl; auto. }
                { reflexivity. }
              }
              { disc_InvObjOwned.
                clear Hci Hoi.
                solve_by_ObjsInvalid_status_false oidx.
              }
            }
          }

          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx0.
              { clear Hci Hoi.
                solve_by_ObjsInvalid_status_false oidx.
              }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx0.
              { solve_ObjsInvalid_trivial. }
              { clear Hci Hoi.
                solve_by_ObjsInvalid_status_false oidx.
              }
            }
          }
        }
      }

      { (* [liInvImmS1] *)
        disc_rule_conds_ex.
        derive_child_st cidx.
        split; [solve_AtomicInv_rqUp|].
        pose proof H4 as Hi; phide Hi; rename H34 into Hi.

        case_InvExcl_me_others.
        { disc_InvExcl_this.
          { disc_InvObjExcl0_apply.
            split; [solve_ObjsInvalid_trivial|solve_MsgsP].
          }
          { disc_InvObjOwned.
            split; [solve_ObjsInvalid_trivial|solve_MsgsP].
          }
          { split_InvDirInv;
              [|exfalso;
                pose proof (getDir_removeSharer_sound cidx0 cidx os#[dir]);
                simpl in *; solve_msi].
            case_idx_eq cidx0 cidx.
            { disc_AtomicMsgOutsInv cidx.
              disc_MsgPred.
              eapply InvExcl_inv_ObjsInvalid; eauto.
              preveal Hi; assumption.
            }
            { solve_ObjsInvalid_trivial.
              simpl in H39; rewrite getDir_removeSharer_neq in H39 by assumption.
              apply H35; assumption.
            }
          }
        }

        { disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            split; [|solve_MsgsP].
            eapply ObjsInvalid_state_transition_sound; eauto.
            { solve_ObjsInvalid_trivial. }
            { simpl; right; apply getDir_S_imp in H30; dest; auto. }
          }
          { disc_InvObjOwned.
            split; [|solve_MsgsP].
            eapply ObjsInvalid_state_transition_sound; eauto.
            { solve_ObjsInvalid_trivial. }
            { simpl; right; apply getDir_S_imp in H30; dest; auto. }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx0.
              { eapply ObjsInvalid_state_transition_sound; eauto.
                { solve_ObjsInvalid_trivial. }
                { simpl; right; apply getDir_S_imp in H30; dest; auto. }
              }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx0.
              { solve_ObjsInvalid_trivial. }
              { eapply ObjsInvalid_state_transition_sound; eauto.
                { solve_ObjsInvalid_trivial. }
                { simpl; right; apply getDir_S_imp in H30; dest; auto. }
              }
            }
          }
        }
      }

      { (* [liInvImmWBI] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_rqUp. }
        { solve_InvExcl_trivial. }
      }

      { (* [liInvImmWBS1] *)
        disc_rule_conds_ex.
        derive_child_st cidx.
        split; [solve_AtomicInv_rqUp|].
        pose proof H4 as Hi; phide Hi; rename H34 into Hi.

        case_InvExcl_me_others.
        { disc_InvExcl_this.
          { disc_InvObjExcl0_apply.
            split; [solve_ObjsInvalid_trivial|solve_MsgsP].
          }
          { disc_InvObjOwned.
            split; [solve_ObjsInvalid_trivial|solve_MsgsP].
          }
          { split_InvDirInv;
              [|exfalso;
                pose proof (getDir_removeSharer_sound cidx0 cidx os#[dir]);
                simpl in *; solve_msi].
            case_idx_eq cidx0 cidx.
            { disc_AtomicMsgOutsInv cidx.
              disc_MsgPred.
              eapply InvExcl_inv_ObjsInvalid; eauto.
              preveal Hi; assumption.
            }
            { solve_ObjsInvalid_trivial.
              simpl in H39; rewrite getDir_removeSharer_neq in H39 by assumption.
              apply H35; assumption.
            }
          }
        }

        { disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            split; [|solve_MsgsP].
            eapply ObjsInvalid_state_transition_sound; eauto.
            { solve_ObjsInvalid_trivial. }
            { simpl; right; apply getDir_S_imp in H30; dest; auto. }
          }
          { disc_InvObjOwned.
            split; [|solve_MsgsP].
            eapply ObjsInvalid_state_transition_sound; eauto.
            { solve_ObjsInvalid_trivial. }
            { simpl; right; apply getDir_S_imp in H30; dest; auto. }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx0.
              { eapply ObjsInvalid_state_transition_sound; eauto.
                { solve_ObjsInvalid_trivial. }
                { simpl; right; apply getDir_S_imp in H30; dest; auto. }
              }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx0.
              { solve_ObjsInvalid_trivial. }
              { eapply ObjsInvalid_state_transition_sound; eauto.
                { solve_ObjsInvalid_trivial. }
                { simpl; right; apply getDir_S_imp in H30; dest; auto. }
              }
            }
          }
        }
      }

      { (* [liInvImmWBM] *)
        disc_rule_conds_ex.
        derive_child_st cidx.
        derive_NoRsI_by_rqUp cidx msgs.
        rename H33 into Hrsi.

        assert (ObjsInvalid
                  (fun idx => In idx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx))
                  (oss +[oidx <- (msg_value rmsg, (true, (msiM, (setDirI, snd (snd (snd (snd os)))))))])
                  (enqMP (downTo cidx) {| msg_id := msiInvRs;
                                          msg_type := MRs;
                                          msg_addr := msg_addr rmsg;
                                          msg_value := 0 |}
                         (deqMP (rqUpFrom cidx) msgs))) as Hci.
        { disc_AtomicMsgOutsInv cidx.
          disc_MsgPred.
          eapply InvExcl_inv_ObjsInvalid; eauto.
        }

        assert (ObjsInvalid
                  (fun idx => ~ In idx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx))
                  oss msgs) as Hcci.
        { disc_InvExcl oidx.
          disc_InvDirInv cidx.
          apply H35.
          simpl; solve_msi.
        }

        assert (ObjsInvalid
                  (fun idx => oidx <> idx)
                  (oss +[oidx <- (msg_value rmsg, (true, (msiM, (setDirI, snd (snd (snd (snd os)))))))])
                  (enqMP (downTo cidx) {| msg_id := msiInvRs;
                                          msg_type := MRs;
                                          msg_addr := msg_addr rmsg;
                                          msg_value := 0 |}
                         (deqMP (rqUpFrom cidx) msgs))) as Hoi.
        { eapply ObjsInvalid_invRs_composed.
          { solve_ObjsInvalid_trivial.
            eapply ObjsInvalid_impl; [apply Hcci|].
            simpl; intros.
            intro Hx; elim H33.
            eapply subtreeIndsOf_child_SubList; eauto.
          }
          { apply ObjsInvalid_child_forall; intros rcidx ?.
            case_idx_eq rcidx cidx; [assumption|].
            solve_ObjsInvalid_trivial.
            disc_InvExcl oidx.
            disc_InvDirInv rcidx.
            apply H35.
            apply getDir_M_imp in H30; dest; subst.
            eapply getDir_excl_neq; eauto.
          }
        }

        split; [solve_AtomicInv_rqUp|].
        case_InvExcl_me_others.
        { disc_InvExcl_this.
          { disc_InvObjExcl0; split; [apply Hoi|].
            disc_MsgConflictsInv oidx.
            solve_MsgsP.
            eapply ObjInvalid_NoCohMsgs; eauto.
            eapply ObjsInvalid_ObjInvalid; try exact Hcci; eauto.
            simpl; intro; solve_by_topo_false.
          }
          { disc_InvDirInv cidx.
            simpl in *; rewrite H30 in H34.
            specialize (H35 ltac:(solve_msi)).
            disc_InvObjOwned; split.
            { solve_ObjsInvalid_trivial.
              eapply ObjsInvalid_impl; [apply H35|].
              simpl; intros.
              intro Hx; elim H38.
              eapply subtreeIndsOf_child_SubList with (cidx:= cidx); eauto.
            }
            { disc_MsgConflictsInv oidx.
              apply parent_not_in_subtree in H13; auto.
              specialize (H35 _ H13); rewrite H15 in H35; simpl in H35.
              solve_MsgsP.
              eapply ObjInvalid_NoCohMsgs; eauto.
            }
          }
          { split_InvDirInv; [|exfalso; rewrite getDir_setDirI in H38; solve_msi].
            case_idx_eq cidx0 cidx.
            { apply Hci. }
            { solve_ObjsInvalid_trivial.
              apply H34.
              apply getDir_M_imp in H30; dest; subst.
              eapply getDir_excl_neq;
                [reflexivity|simpl; solve_msi|assumption].
            }
          }
        }

        { assert (msiS <= cost#[status]).
          { (** TODO: bring [disc_InvWB] to here? *)
            move Hwb at bottom.
            specialize (Hwb _ _ H13); simpl in Hwb.
            disc_rule_conds_ex.
            apply Hwb.
            { apply getDir_M_imp in H30; dest.
              repeat split; try assumption.
            }
            { eexists (_, _); split; [apply FirstMP_InMP; eassumption|].
              unfold sigOf; simpl; congruence.
            }
          }

          disc_InvExcl_others.
          { case_idx_eq eidx cidx.
            { red; intros [? ?]; exfalso.
              apply NoRsI_MsgExistsSig_InvRs_false in H38; auto.
              eexists (_, _); split.
              { apply InMP_or_enqMP; left; simpl; auto. }
              { reflexivity. }
            }
            { disc_InvObjExcl0.
              destruct H37.
              clear Hci Hcci.
              exfalso; eapply ObjsInvalid_obj_status_false with (oidx := eidx);
                eauto; simpl in *; auto.
              { solve_MsgsP. }
              { mred. }
              { solve_msi. }
            }
          }

          { case_in_subtree oidx eidx.
            { disc_InvObjOwned.
              split; [solve_ObjsInvalid_trivial|solve_MsgsP].
            }
            { case_in_subtree cidx eidx.
              { eapply inside_child_outside_parent_case in i; eauto; subst.
                red; intros [? ?]; exfalso.
                apply NoRsI_MsgExistsSig_InvRs_false in H38; auto.
                eexists (_, _); split.
                { apply InMP_or_enqMP; left; simpl; auto. }
                { reflexivity. }
              }
              { disc_InvObjOwned.
                clear Hci Hcci Hoi; solve_by_ObjsInvalid_status_false cidx.
              }
            }
          }

          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx0.
              { clear Hci Hcci Hoi.
                eapply inside_child_in in i; eauto.
                solve_by_ObjsInvalid_status_false cidx.
              }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx0.
              { solve_ObjsInvalid_trivial. }
              { eapply outside_child_in in n0; eauto.
                destruct n0; subst; [disc_rule_conds_ex|].
                clear Hci Hcci Hoi.
                solve_by_ObjsInvalid_status_false cidx.
              }
            }
          }
        }
      }
    }

    dest_in.

    { (* [liGetSRsDownDownS] *)
      disc_rule_conds_ex.
      derive_footprint_info_basis oidx.
      disc_MsiUpLockInv oidx.
      derive_child_chns cidx.
      disc_rule_conds_ex.

      split.
      { solve_AtomicInv_rsDown. }
      { solve_InvExcl_trivial.
        case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { split_InvDirInv.
            { disc_dir.
              specialize (H36 H40).
              solve_ObjsInvalid_trivial.
            }
            { exfalso.
              disc_dir.
              pose proof (getDir_st_sound (fst (snd (snd (snd os)))) cidx0 ltac:(solve_msi)).
              solve_msi.
            }
          }
        }

        { disc_MsgConflictsInv oidx.
          disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            solve_by_ObjsInvalid_rsS_false oidx.
          }
          { case_InvObjOwned.
            { solve_by_ObjsInvalid_rsS_false oidx. }
            { disc_ObjsInvalid_by oidx0; case_ObjInvalid.
              { case_idx_eq oidx0 cidx; [|solve_ObjInvalid0].
                eapply outside_parent_out in H47; eauto.
                solve_by_ObjsInvalid_rsS_false oidx.
              }
              { solve_ObjInvRs. }
            }
            { case_idx_eq cidx eidx; [|solve_MsgsP].
              exfalso.
              case_in_subtree oidx eidx; [solve_by_topo_false|].
              solve_by_ObjsInvalid_rsS_false oidx.
            }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx0.
              { solve_by_ObjsInvalid_rsS_false oidx. }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx0.
              { solve_ObjsInvalid_trivial. }
              { solve_by_ObjsInvalid_rsS_false oidx. }
            }
          }
        }
      }
    }

    { (* [liDownSRsUpDownM] *)
      disc_rule_conds_ex.
      disc_MsiDownLockInv oidx Hdlinv.
      derive_footprint_info_basis oidx.

      split.
      { solve_AtomicInv_rsUps_rsDown Hrsd. }
      { apply subtreeChildrenIndsOf_parentIdxOf in H29; auto.
        case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { remember (dir_excl _) as rcidx.
            disc_InvDirInv rcidx.
            rewrite getDir_excl_eq in H39; [|assumption|intuition solve_msi].
            simpl in *; rewrite H23 in H39.
            specialize (H39 ltac:(solve_msi)).
            clear Heqrcidx.

            disc_InvObjOwned; split.
            { solve_ObjsInvalid_trivial.
              eapply ObjsInvalid_impl; [eassumption|].
              simpl; intros.
              intro Hx; elim H42.
              eapply subtreeIndsOf_child_SubList with (cidx:= rcidx); eauto.
            }
            { disc_MsgConflictsInv oidx.
              apply parent_not_in_subtree in H29; auto.
              specialize (H39 _ H29); rewrite H15 in H39; simpl in H39.
              solve_MsgsP.
              eapply ObjInvalid_NoCohMsgs; eauto.
            }
          }
          { remember (dir_excl _) as rcidx.
            split_InvDirInv.
            { apply getDir_setDirS_I_imp in H42.
              case_idx_eq x cidx; [exfalso; elim H42; left; reflexivity|].
              case_idx_eq rcidx cidx; [exfalso; elim H42; right; left; reflexivity|].
              solve_ObjsInvalid_trivial.
              apply H38.
              eapply getDir_excl_neq; [reflexivity|intuition solve_msi|simpl; congruence].
            }
            { exfalso.
              pose proof (getDir_setDirS_sound cidx [x; rcidx]).
              simpl in *; solve_msi.
            }
          }
        }

        { pose proof Hpmcf as Hpmcf'; phide Hpmcf'; rename H38 into Hpmcf'.
          disc_MsgConflictsInv oidx.
          remember (dir_excl _) as rcidx; clear Heqrcidx.
          disc_AtomicMsgOutsInv rcidx.

          derive_child_st rcidx.
          disc_MsgPred.
          preveal Hpmcf'; disc_MsgConflictsInv rcidx.

          disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            exfalso.
            case_idx_eq eidx rcidx.
            { disc_rule_conds; disc_ObjExcl0; solve_msi. }
            { solve_by_ObjsInvalid_downRsS_false rcidx. }
          }
          { case_in_subtree rcidx eidx;
              [|disc_InvObjOwned; solve_by_ObjsInvalid_downRsS_false rcidx].
            case_idx_eq eidx rcidx;
              [disc_rule_conds_ex; disc_InvObjOwned; simpl in *; congruence|].
            disc_InvObjOwned; split.
            { assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) eidx)).
              { eapply inside_parent_in with (cidx:= rcidx); eauto. }
              solve_ObjsInvalid_trivial.
            }
            { case_idx_eq x eidx; [|solve_MsgsP].
              assert (~ In rcidx (subtreeIndsOf (fst (tree2Topo tr 0)) eidx)).
              { intro; solve_by_topo_false. }
              solve_by_ObjsInvalid_downRsS_false rcidx.
            }
          }
          { split_InvDirInv_apply.
            { case_in_subtree x cidx.
              { case_idx_eq x cidx; [disc_rule_conds|].
                assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx)).
                { eapply inside_parent_in with (cidx:= x); eauto. }
                assert (In rcidx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx)).
                { eapply inside_child_in; eauto. }
                solve_by_ObjsInvalid_downRsS_false rcidx.
              }
              { case_in_subtree rcidx cidx; [solve_by_ObjsInvalid_downRsS_false rcidx|].
                solve_ObjsInvalid_trivial.
              }
            }
            { case_in_subtree rcidx cidx;
                [|solve_by_ObjsInvalid_downRsS_false rcidx].
              case_idx_eq rcidx cidx; [disc_rule_conds|].
              assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx)).
              { eapply inside_parent_in with (cidx:= rcidx); eauto. }
              solve_ObjsInvalid_trivial.
            }
          }
        }
      }
    }

    { (* [liDownSImm] *)
      disc_rule_conds_ex.
      derive_NoRsI_by_rqDown oidx msgs.

      split.
      { solve_AtomicInv_rqDown_rsUp.
        solve_DownRsSPred.
      }
      { case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { split_InvDirInv_apply.
            { solve_ObjsInvalid_trivial. }
            { exfalso; disc_dir.
              pose proof (getDir_st_sound (fst (snd (snd (snd os)))) cidx ltac:(solve_msi)).
              solve_msi.
            }
          }
        }
        { disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            solve_by_ObjsInvalid_status_false oidx.
          }
          { case_InvObjOwned.
            { solve_by_ObjsInvalid_status_false oidx. }
            { disc_ObjsInvalid_by oidx0.
              case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
            }
            { solve_MsgsP. }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx.
              { solve_by_ObjsInvalid_status_false oidx. }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx.
              { solve_ObjsInvalid_trivial. }
              { solve_by_ObjsInvalid_status_false oidx. }
            }
          }
        }
      }
    }

    { (* [liDownSRqDownDownM] *)
      disc_rule_conds_ex; split.
      { remember (dir_excl _) as cidx; clear Heqcidx.
        solve_AtomicInv_rqDown_rqDowns.
        apply subtreeChildrenIndsOf_parentIdxOf in H23; auto.
        derive_child_chns cidx.
        repeat constructor; simpl; eauto.
      }
      { solve_InvExcl_trivial. }
    }

    { (* [liDownSRsUpUp] *)
      disc_rule_conds_ex.
      disc_MsiDownLockInv oidx Hdlinv.
      derive_footprint_info_basis oidx; [solve_midx_false|].
      pick_rsUp_single.

      split.
      { solve_AtomicInv_rsUps_rsUp.
        solve_DownRsSPred.
      }
      { apply subtreeChildrenIndsOf_parentIdxOf in H29; auto.
        case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { remember (dir_excl _) as rcidx.
            split_InvDirInv.
            { apply getDir_setDirS_I_imp in H42.
              case_idx_eq rcidx cidx0; [exfalso; elim H42; left; reflexivity|clear H42].
              solve_ObjsInvalid_trivial.
              apply H38.
              eapply getDir_excl_neq; [reflexivity|intuition solve_msi|simpl; congruence].
            }
            { exfalso.
              pose proof (getDir_setDirS_sound cidx0 [rcidx]).
              simpl in *; solve_msi.
            }
          }
        }

        { pose proof Hpmcf as Hpmcf'; phide Hpmcf'; rename H37 into Hpmcf'.
          disc_MsgConflictsInv oidx.
          remember (dir_excl _) as rcidx; clear Heqrcidx.
          disc_AtomicMsgOutsInv rcidx.

          derive_child_st rcidx.
          disc_MsgPred.
          preveal Hpmcf'; disc_MsgConflictsInv rcidx.

          disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            exfalso.
            case_idx_eq eidx rcidx.
            { disc_rule_conds; disc_ObjExcl0; solve_msi. }
            { solve_by_ObjsInvalid_downRsS_false rcidx. }
          }
          { case_in_subtree rcidx eidx;
              [|disc_InvObjOwned; solve_by_ObjsInvalid_downRsS_false rcidx].
            case_idx_eq eidx rcidx;
              [disc_rule_conds; disc_InvObjOwned; simpl in *; congruence|].
            disc_InvObjOwned; split.
            { assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) eidx)).
              { eapply inside_parent_in with (cidx:= rcidx); eauto. }
              solve_ObjsInvalid_trivial.
            }
            { solve_MsgsP. }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx0.
              { assert (In rcidx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx0)).
                { eapply inside_child_in; eauto. }
                solve_by_ObjsInvalid_downRsS_false rcidx.
              }
              { case_in_subtree rcidx cidx0; [solve_by_ObjsInvalid_downRsS_false rcidx|].
                solve_ObjsInvalid_trivial.
              }
            }
            { case_in_subtree rcidx cidx0;
                [|solve_by_ObjsInvalid_downRsS_false rcidx].
              case_idx_eq rcidx cidx0; [disc_rule_conds|].
              assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx0)).
              { eapply inside_parent_in with (cidx:= rcidx); eauto. }
              solve_ObjsInvalid_trivial.
            }
          }
        }
      }
    }

    { (* [liGetMRsDownDownDirI] *)
      disc_rule_conds_ex.
      derive_footprint_info_basis oidx.
      disc_MsiUpLockInv oidx.
      derive_child_chns cidx.
      disc_MsgConflictsInv oidx.
      disc_rule_conds_ex.

      rename H26 into Hprec. (* the precondition about status and ownership bit *)
      assert (ObjsInvalid (fun idx => ~ In idx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx))
                          (oss +[oidx <- (fst os,
                                          (false,
                                           (invalidate (fst (snd (snd os))),
                                            (setDirM cidx, snd (snd (snd (snd os)))))))])
                          (deqMP (downTo oidx) msgs)) as Hoi.
      { disc_AtomicMsgOutsInv oidx.
        disc_InvExcl oidx.
        destruct Hprec; dest.
        { eapply ObjsInvalid_rsM_consumed; eauto.
          { apply tl_In; assumption. }
          { assumption. }
          { simpl; solve_msi. }
        }
        { eapply ObjsInvalid_out_composed; eauto.
          { solve_ObjsInvalid_trivial.
            apply H34; auto.
          }
          { mred. }
          { left; repeat split; [simpl; solve_msi|discriminate|].
            eapply NoCohMsgs_rsDown_deq; eauto.
          }
          { intros.
            solve_ObjsInvalid_trivial.
            disc_InvDirInv rcidx.
            apply H48.
            eapply getDir_LastSharer_neq; try eassumption.
            eapply getDir_LastSharer_eq; eassumption.
          }
        }
      }

      split.
      { solve_AtomicInv_rsDown.
        disc_AtomicMsgOutsInv oidx.
        disc_MsgPred.
        disc_InvExcl oidx.
        solve_msg_pred_base.
        solve_ObjsInvalid_trivial.
      }

      { solve_InvExcl_trivial.
        case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { pose proof H34. (* [InvDirInv] *)
            split_InvDirInv.
            { case_idx_eq cidx cidx0; [disc_dir; discriminate|].
              solve_ObjsInvalid_trivial.
              apply H36.
              destruct Hprec; dest.
              { apply getDir_st_I; assumption. }
              { eapply getDir_LastSharer_neq; eauto.
                eapply getDir_LastSharer_eq; auto.
              }
            }
            { case_idx_eq cidx cidx0; [|disc_dir; solve_msi].
              disc_AtomicMsgOutsInv oidx.
              disc_MsgPred.
              solve_ObjsInvalid_trivial.
            }
          }
        }

        { disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            solve_by_ObjsInvalid_rsM_false oidx.
          }
          { case_InvObjOwned.
            { solve_by_ObjsInvalid_rsM_false oidx. }
            { disc_ObjsInvalid_by oidx0; case_ObjInvalid.
              { case_idx_eq oidx0 cidx; [|solve_ObjInvalid0].
                eapply outside_parent_out in H46; eauto.
                solve_by_ObjsInvalid_rsM_false oidx.
              }
              { solve_ObjInvRs. }
            }
            { case_idx_eq cidx eidx; [|solve_MsgsP].
              exfalso.
              case_in_subtree oidx eidx; [solve_by_topo_false|].
              solve_by_ObjsInvalid_rsM_false oidx.
            }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx0.
              { solve_by_ObjsInvalid_rsM_false oidx. }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx0.
              { solve_ObjsInvalid_trivial. }
              { solve_by_ObjsInvalid_rsM_false oidx. }
            }
          }
        }
      }
    }

    { (* [liGetMRsDownRqDownDirS] *)
      disc_rule_conds_ex.
      derive_footprint_info_basis oidx.
      derive_child_chns cidx.
      disc_MsgConflictsInv oidx.
      disc_rule_conds_ex.

      split.
      { solve_AtomicInv_rsDown.
        (** TODO: Ltac? *)
        apply Forall_forall; intros.
        apply in_map_iff in H1; dest; subst.
        repeat constructor; try (red; simpl; intros; intuition discriminate).
      }
      { solve_InvExcl_trivial.
        case_InvExcl_me_others.
        { disc_InvExcl_this.
          { disc_InvObjExcl0_apply; split.
            { solve_ObjsInvalid_trivial. }
            { solve_MsgsP. }
          }
          { disc_AtomicMsgOutsInv oidx.
            disc_MsgPred.
            disc_InvObjOwned; split.
            { solve_ObjsInvalid_trivial. }
            { eapply NoCohMsgs_rsDown_deq; eauto. }
          }
          { split_InvDirInv_apply.
            { solve_ObjsInvalid_trivial. }
            { simpl in H37.
              pose proof (getDir_st_sound (fst (snd (snd (snd os)))) cidx0 ltac:(solve_msi)).
              solve_msi.
            }
          }
        }

        { disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            solve_by_ObjsInvalid_rsM_false oidx.
          }
          { case_InvObjOwned.
            { solve_by_ObjsInvalid_rsM_false oidx. }
            { disc_ObjsInvalid_by oidx0.
              case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
            }
            { solve_MsgsP. }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx0.
              { solve_by_ObjsInvalid_rsM_false oidx. }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx0.
              { solve_ObjsInvalid_trivial. }
              { solve_by_ObjsInvalid_rsM_false oidx. }
            }
          }
        }
      }
    }

    { (* [liDownIRsUpDownS] *)
      disc_rule_conds_ex.
      disc_MsiDownLockInv oidx Hdlinv.
      derive_footprint_info_basis oidx.
      destruct H28; [simpl in *; dest|solve_msi; fail].

      (** 1) Each RsUp message is from a child *)
      assert (Forall
                (fun midx =>
                   exists rcidx,
                     parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx /\
                     midx = rsUpFrom rcidx)
                (idsOf rins)) as Hrss.
      { apply Forall_forall; intros rsUp ?.
        eapply RqRsDownMatch_rs_rq in H36; [|rewrite <-H13; eassumption].
        destruct H36 as [cidx [down ?]]; dest.
        derive_child_chns cidx; repeat disc_rule_minds.
        eauto.
      }

      (** 2-1) Each child (except the requestor) either sent RsUp or is in DirI *)
      assert (forall rcidx,
                 parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx ->
                 x <> rcidx ->
                 if in_dec idx_dec (rsUpFrom rcidx) (idsOf rins)
                 then True
                 else getDir rcidx os#[dir] = msiI) as Hcs.
      { intros.
        destruct (in_dec idx_dec rcidx
                         (remove idx_dec x (dir_sharers (fst (snd (snd (snd os))))))).
        { find_if_inside; [auto|].
          elim n; rewrite H13, H39; apply in_map; assumption.
        }
        { find_if_inside; [auto|].
          apply getDir_S_non_sharer; [assumption|].
          intro Hx; elim n.
          apply in_remove_neq; auto.
        }
      }

      (** 2-2) Each child subtree (except the requestor) satisfies [ObjsInvalid] *)
      assert (forall rcidx,
                 parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx ->
                 x <> rcidx ->
                 forall nost rsTo,
                   ObjsInvalid
                     (fun idx =>
                        In idx (subtreeIndsOf (fst (tree2Topo tr 0)) rcidx))
                     (oss +[oidx <- nost])
                     (enqMP (downTo x) rsTo (deqMsgs (idsOf rins) msgs))) as Hcsi.
      { intros.
        specialize (Hcs _ H40 H41); find_if_inside.
        { apply in_map_iff in i; destruct i as [[midx rs] ?]; simpl in *; dest; subst.
          rewrite Forall_forall in H14; specialize (H14 _ H43).
          rewrite Forall_forall in H23; specialize (H23 _ H43); simpl in *.
          pose proof (H3 _ H43) as Hrein.
          disc_AtomicMsgOutsInv rcidx.
          specialize (H45 eq_refl H23 H14); dest.
          derive_child_st rcidx.
          disc_MsgConflictsInv rcidx.
          rewrite H51 in H45; simpl in H45; dest.
          solve_ObjsInvalid_trivial.
          eapply ObjsInvalid_this_rsUps_deqMsgs_silent; eauto.
          apply parent_not_in_subtree; auto.
        }
        { disc_InvExcl oidx.
          red in H43.
          specialize (H43 (tl_In _ _ H8)).
          move H43 at bottom.
          specialize (H43 _ H40); destruct H43 as [? _].
          specialize (H43 Hcs).
          solve_ObjsInvalid_trivial.
          eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
          intro; solve_by_topo_false.
        }
      }

      assert (NoRsI oidx msgs) as Hrsi.
      { move Hidir at bottom.
        specialize (Hidir oidx); simpl in Hidir.
        rewrite H15 in Hidir; simpl in Hidir.
        eapply not_MsgExistsSig_MsgsNotExist; intros;
          inv H40; [|dest_in].
        specialize (Hidir (or_intror (or_intror H41))).
        simpl in *; solve_msi.
      }

      (** 2-2) ObjsInvalid, outside [oidx] *)
      assert (forall nost rsTo,
                 ObjsInvalid
                   (fun idx => ~ In idx (subtreeIndsOf (fst (tree2Topo tr 0)) oidx))
                   (oss +[oidx <- nost])
                   (enqMP (downTo x) rsTo (deqMsgs (idsOf rins) msgs))) as Hoo.
      { intros.
        solve_ObjsInvalid_trivial.
        eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto;
          [|intro; solve_by_topo_false].
        disc_InvExcl oidx.
        specialize (H40 (conj H28 Hrsi)); dest; assumption.
      }

      (** 2-3) The target object itself gets invalid *)
      assert (forall rsTo,
                 ObjInvalid0
                   oidx (fst os,
                         (false,
                          (invalidate (fst (snd (snd os))),
                           (setDirM x, snd (snd (snd (snd os)))))))
                   (enqMP (downTo x) rsTo (deqMsgs (idsOf rins) msgs))) as Hoi.
      { intros; repeat split; [simpl; solve_msi|discriminate|].
        disc_InvExcl oidx.
        specialize (H40 (conj H28 Hrsi)); dest; solve_MsgsP.
      }

      (** 3) Predicate for [msiRsM] *)
      assert (ObjsInvalid
                (fun idx => ~ In idx (subtreeIndsOf (fst (tree2Topo tr 0)) x))
                (oss +[oidx <- (fst os,
                                (false,
                                 (invalidate (fst (snd (snd os))),
                                  (setDirM x, snd (snd (snd (snd os)))))))])
                (enqMP (downTo x)
                       {| msg_id := msiRsM;
                          msg_type := MRs;
                          msg_addr := msg_addr msg;
                          msg_value := 0 |} (deqMsgs (idsOf rins) msgs))) as Hrc.
      { intros.
        eapply ObjsInvalid_out_composed with (oidx:= oidx); eauto.
        { mred. }
        { left; apply Hoi. }
      }

      split.
      { solve_AtomicInv_rsUps_rsDown Hrsd.
        red; simpl; intros; inv H40.
        rewrite <-H13; eapply Hrc.
      }

      { case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { split_InvDirInv.
            { case_idx_eq x cidx;
                [rewrite getDir_setDirM_eq in H44; discriminate|clear H44].
              rewrite <-H13; eapply Hcsi; eauto.
            }
            { case_idx_eq x cidx;
                [clear H44
                |simpl in H44; rewrite getDir_setDirM_neq in H44 by assumption;
                 solve_msi].
              rewrite <-H13; eapply Hrc.
            }
          }
        }

        { disc_InvExcl_others.
          { disc_InvObjExcl0.
            rewrite <-H13 in H43.
            apply ObjExcl0_other_msg_id_deqMsgs_inv in H43; auto.
            2: { eapply Forall_impl; [|apply H14]; simpl; intros.
                 rewrite H44; discriminate.
            }
            specialize (H4 H43); dest.
            exfalso.
            disc_ObjsInvalid_by oidx.
            rewrite H15 in H45; simpl in H45.
            destruct H45.
            { destruct H45 as [? [? ?]]; auto. }
            { eapply NoRsI_MsgExistsSig_InvRs_false; eauto. }
          }

          { red; intros [? ?].
            assert (NoRsI eidx msgs).
            { disc_MsgsP H44.
              rewrite <-H13 in H44; simpl in H44.
              apply MsgsP_other_msg_id_deqMsgs_inv in H44; auto.
              simpl; apply (DisjList_spec_2 idx_dec); intros; dest_in.
              intro; dest_in.
              apply in_map_iff in H32; destruct H32 as [[rmidx rmsg] [? ?]]; simpl in *.
              rewrite Forall_forall in H14; specialize (H14 _ H45); simpl in *.
              rewrite H14 in H32; discriminate.
            }
            specialize (H41 (conj H43 H45)); dest.

            case_in_subtree oidx eidx;
              [|clear Hrc; solve_by_ObjsInvalid_dir_false oidx].
            split.
            { solve_ObjsInvalid_trivial.
              rewrite <-H13.
              eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
            }
            { case_idx_eq x eidx; [|solve_MsgsP].
              exfalso.
              apply parent_not_in_subtree in i; auto.
            }
          }

          { split_InvDirInv_apply.
            { case_in_subtree x cidx.
              { case_idx_eq x cidx; [disc_rule_conds|].
                assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx)).
                { eapply inside_parent_in with (cidx:= x); eauto. }
                clear Hrc; solve_by_ObjsInvalid_dir_false oidx.
              }
              { solve_ObjsInvalid_trivial.
                rewrite <-H13.
                eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
                intro; solve_by_topo_false.
              }
            }
            { case_in_subtree oidx cidx;
                [|clear Hrc; solve_by_ObjsInvalid_dir_false oidx].
              solve_ObjsInvalid_trivial.
              rewrite <-H13.
              eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
            }
          }
        }
      }
    }

    { (* [liDownIRsUpDownM] *)
      disc_rule_conds_ex.
      disc_MsiDownLockInv oidx Hdlinv.
      derive_footprint_info_basis oidx.
      destruct H28; [solve_msi; fail|simpl in *; dest].

      (** 1) Each RsUp message is from a child *)
      assert (Forall
                (fun midx =>
                   exists rcidx,
                     parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx /\
                     midx = rsUpFrom rcidx)
                (idsOf rins)) as Hrss.
      { apply Forall_forall; intros rsUp ?.
        eapply RqRsDownMatch_rs_rq in H36; [|rewrite <-H13; eassumption].
        destruct H36 as [cidx [down ?]]; dest.
        derive_child_chns cidx; repeat disc_rule_minds.
        eauto.
      }

      (** 2-1) Each child (except the requestor) either sent RsUp or is in DirI *)
      assert (forall rcidx,
                 parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx ->
                 x <> rcidx ->
                 if in_dec idx_dec (rsUpFrom rcidx) (idsOf rins)
                 then True
                 else getDir rcidx os#[dir] = msiI) as Hcs.
      { intros.
        case_idx_eq rcidx (dir_excl (fst (snd (snd (snd os))))).
        { find_if_inside; [auto|].
          elim n; rewrite H13, H38; left; reflexivity.
        }
        { find_if_inside; [auto|erewrite getDir_excl_neq; eauto]. }
      }

      (** 2-2) Each child subtree (except the requestor) satisfies [ObjsInvalid] *)
      assert (forall rcidx,
                 parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx ->
                 x <> rcidx ->
                 forall nost rsTo,
                   ObjsInvalid
                     (fun idx =>
                        In idx (subtreeIndsOf (fst (tree2Topo tr 0)) rcidx))
                     (oss +[oidx <- nost])
                     (enqMP (downTo x) rsTo (deqMsgs (idsOf rins) msgs))) as Hcsi.
      { intros.
        specialize (Hcs _ H39 H40); find_if_inside.
        { apply in_map_iff in i; destruct i as [[midx rs] ?]; simpl in *; dest; subst.
          rewrite Forall_forall in H14; specialize (H14 _ H42).
          rewrite Forall_forall in H23; specialize (H23 _ H42); simpl in *.
          pose proof (H3 _ H42) as Hrein.
          disc_AtomicMsgOutsInv rcidx.
          specialize (H45 eq_refl H23 H14); dest.
          derive_child_st rcidx.
          disc_MsgConflictsInv rcidx.
          rewrite H50 in H45; simpl in H45; dest.
          solve_ObjsInvalid_trivial.

          eapply ObjsInvalid_in_composed; eauto.
          { left; repeat split; [simpl; solve_msi|simpl; rewrite H59; discriminate|].
            apply NoCohMsgs_rsUps_deq; eauto.
            { eapply Forall_impl; [|apply Hrss].
              simpl; intros; dest; eauto.
            }
            { apply in_map with (f:= idOf) in H42; assumption. }
            { rewrite Forall_forall in H17; specialize (H17 _ H42).
              eapply NoCohMsgs_rsUp_deq; eauto.
            }
          }
          { eapply ObjsInvalid_this_rsUps_deqMsgs_silent; eauto.
            intro Hx; destruct Hx as [ccidx [? ?]].
            eapply subtreeIndsOf_child_SubList in H62; eauto.
            apply parent_not_in_subtree in H39; auto.
          }
        }
        { disc_InvExcl oidx.
          specialize (H42 (tl_In _ _ H8)).
          move H42 at bottom.
          specialize (H42 _ H39); destruct H42 as [? _].
          specialize (H42 Hcs).
          solve_ObjsInvalid_trivial.
          eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
          intro; solve_by_topo_false.
        }
      }

      assert (NoRsI oidx msgs) as Hrsi.
      { move Hidir at bottom.
        specialize (Hidir oidx); simpl in Hidir.
        rewrite H15 in Hidir; simpl in Hidir.
        eapply not_MsgExistsSig_MsgsNotExist; intros;
          inv H39; [|dest_in].
        specialize (Hidir (or_intror (or_intror H40))).
        simpl in *; solve_msi.
      }

      (** 2-2) ObjsInvalid, outside [oidx] *)
      assert (forall nost rsTo,
                 ObjsInvalid
                   (fun idx => ~ In idx (subtreeIndsOf (fst (tree2Topo tr 0)) oidx))
                   (oss +[oidx <- nost])
                   (enqMP (downTo x) rsTo (deqMsgs (idsOf rins) msgs))) as Hoo.
      { intros.
        solve_ObjsInvalid_trivial.
        eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto;
          [|intro; solve_by_topo_false].
        disc_InvExcl oidx.
        specialize (H40 (tl_In _ _ H8)).
        apply subtreeChildrenIndsOf_parentIdxOf in H37; auto.
        specialize (H40 _ H37); destruct H40 as [_ ?].
        rewrite getDir_excl_eq in H40; [|reflexivity|intuition solve_msi].
        specialize (H40 ltac:(simpl in *; solve_msi)).
        eapply ObjsInvalid_impl; [eassumption|].
        simpl; intros.
        intro Hx; elim H41.
        eapply subtreeIndsOf_child_SubList with (cidx:= dir_excl _); eauto.
      }

      (** 2-3) The target object itself gets invalid *)
      assert (forall rsTo,
                 ObjInvalid0
                   oidx (fst os,
                         (false,
                          (invalidate (fst (snd (snd os))),
                           (setDirM x, snd (snd (snd (snd os)))))))
                   (enqMP (downTo x) rsTo (deqMsgs (idsOf rins) msgs))) as Hoi.
      { intros; repeat split; [simpl; solve_msi|discriminate|].
        disc_InvExcl oidx.
        specialize (H40 (tl_In _ _ H8)).
        apply subtreeChildrenIndsOf_parentIdxOf in H37; auto.
        specialize (H40 _ H37); destruct H40 as [_ ?].
        rewrite getDir_excl_eq in H40; [|reflexivity|intuition solve_msi].
        specialize (H40 ltac:(simpl in *; solve_msi)).
        apply parent_not_in_subtree in H37; auto.
        specialize (H40 _ H37).
        rewrite H15 in H40; simpl in H40.
        solve_MsgsP.
        disc_MsgConflictsInv oidx.
        eapply ObjInvalid_NoCohMsgs; eauto.
      }

      (** 3) Predicate for [msiRsM] *)
      assert (ObjsInvalid
                (fun idx => ~ In idx (subtreeIndsOf (fst (tree2Topo tr 0)) x))
                (oss +[oidx <- (fst os,
                                (false,
                                 (invalidate (fst (snd (snd os))),
                                  (setDirM x, snd (snd (snd (snd os)))))))])
                (enqMP (downTo x)
                       {| msg_id := msiRsM;
                          msg_type := MRs;
                          msg_addr := msg_addr msg;
                          msg_value := 0 |} (deqMsgs (idsOf rins) msgs))) as Hrc.
      { intros.
        eapply ObjsInvalid_out_composed with (oidx:= oidx); eauto.
        { mred. }
        { left; apply Hoi. }
      }

      split.
      { solve_AtomicInv_rsUps_rsDown Hrsd.
        red; simpl; intros; inv H39.
        rewrite <-H13; eapply Hrc.
      }

      { case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { split_InvDirInv.
            { case_idx_eq x cidx;
                [rewrite getDir_setDirM_eq in H43; discriminate|clear H43].
              rewrite <-H13; eapply Hcsi; eauto.
            }
            { case_idx_eq x cidx;
                [clear H43
                |simpl in H43; rewrite getDir_setDirM_neq in H43 by assumption;
                 solve_msi].
              rewrite <-H13; eapply Hrc.
            }
          }
        }

        { pose proof Hpmcf as Hpmcf'; phide Hpmcf'; rename H39 into Hpmcf'.
          disc_MsgConflictsInv oidx.

          remember (dir_excl _) as cidx; clear Heqcidx.
          rewrite H38 in H13.
          destruct rins as [|[midx rmsg] rins]; [discriminate|].
          destruct rins; [|discriminate].
          simpl in H13; inv H13.

          (* discharge all predicates in [Forall] *)
          inv H14; inv H17; inv H23; inv Hrss; dest; simpl in *.
          clear H46 H47 H48 H49. (* [Forall _ nil] *)
          inv H14; rename x0 into cidx.
          derive_child_chns cidx; repeat disc_rule_minds.
          (* derive the predicate message for it *)
          apply SubList_cons_inv in H3; dest.
          disc_AtomicMsgOutsInv cidx.

          derive_child_st cidx.
          disc_MsgPred.
          preveal Hpmcf'; disc_MsgConflictsInv cidx.

          disc_InvExcl_others.
          { disc_InvObjExcl0.
            rewrite H38 in H69; simpl in H69.
            eapply ObjExcl0_other_msg_id_deqMP_inv in H69; eauto;
              [|simpl; rewrite H45; discriminate].
            specialize (H4 H69); dest.
            exfalso.
            case_idx_eq eidx cidx.
            { disc_rule_conds_ex; disc_ObjExcl0; solve_msi. }
            { solve_by_ObjsInvalid_downRsIM_false cidx. }
          }

          { red; intros [? ?].
            assert (NoRsI eidx msgs).
            { disc_MsgsP H70.
              rewrite H38 in H70; simpl in H70.
              eapply MsgsP_other_msg_id_deqMP_inv in H70; eauto.
              simpl; rewrite H45; intuition discriminate.
            }
            specialize (H67 (conj H69 H71)); dest.

            case_in_subtree cidx eidx; [|solve_by_ObjsInvalid_downRsIM_false cidx].
            case_idx_eq eidx cidx; [disc_rule_conds_ex; congruence (* owner true/false *) |].
            split.
            { assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) eidx)).
              { eapply inside_parent_in with (cidx:= cidx); eauto. }
              solve_ObjsInvalid_trivial.
              rewrite H38.
              eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
            }
            { case_idx_eq x eidx; [|solve_MsgsP].
              assert (~ In cidx (subtreeIndsOf (fst (tree2Topo tr 0)) eidx)).
              { intro; solve_by_topo_false. }
              solve_by_ObjsInvalid_downRsIM_false cidx.
            }
          }

          { split_InvDirInv_apply.
            { case_in_subtree x cidx0.
              { case_idx_eq x cidx0; [disc_rule_conds|].
                assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx0)).
                { eapply inside_parent_in with (cidx:= x); eauto. }
                assert (In cidx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx0)).
                { eapply inside_child_in; eauto. }
                solve_by_ObjsInvalid_downRsIM_false cidx.
              }
              { case_in_subtree cidx cidx0; [solve_by_ObjsInvalid_downRsIM_false cidx|].
                solve_ObjsInvalid_trivial.
                rewrite H38.
                eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
                intro; solve_by_topo_false.
              }
            }
            { case_in_subtree cidx cidx0;
                [|solve_by_ObjsInvalid_downRsIM_false cidx].
              case_idx_eq cidx cidx0; [disc_rule_conds|].
              assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx0)).
              { eapply inside_parent_in with (cidx:= cidx); eauto. }
              solve_ObjsInvalid_trivial.
              rewrite H38.
              eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
            }
          }
        }
      }
    }

    { (* [liDownIImmS] *)
      disc_rule_conds_ex.
      derive_NoRsI_by_rqDown oidx msgs.

      split.
      { solve_AtomicInv_rqDown_rsUp.
        { simpl in *; inv H17; mred.
          simpl; intuition solve_msi.
        }
        { simpl in *; inv H17; mred.
          disc_MsgConflictsInv oidx0.
          disc_InvExcl oidx0.
          eapply ObjsInvalid_downRsIS; eauto.
          { apply tl_In; assumption. }
          { assumption. }
          { simpl; solve_msi. }
        }
      }

      { case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { split_InvDirInv_apply.
            { solve_ObjsInvalid_trivial. }
            { exfalso; disc_dir.
              rewrite getDir_st_I in H20 by assumption.
              solve_msi.
            }
          }
        }
        { disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            split; [|solve_MsgsP].
            solve_ObjsInvalid_trivial.
            eapply ObjsInvalid_state_transition_sound; eauto.
            simpl; solve_msi.
          }
          { disc_InvObjOwned.
            split; [|solve_MsgsP].
            solve_ObjsInvalid_trivial.
            eapply ObjsInvalid_state_transition_sound; eauto.
            simpl; solve_msi.
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx.
              { solve_ObjsInvalid_trivial.
                eapply ObjsInvalid_state_transition_sound; eauto.
                simpl; solve_msi.
              }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx.
              { solve_ObjsInvalid_trivial. }
              { solve_ObjsInvalid_trivial.
                eapply ObjsInvalid_state_transition_sound; eauto.
                simpl; solve_msi.
              }
            }
          }
        }
      }
    }

    { (* [liDownIImmM] *)
      disc_rule_conds_ex.
      derive_NoRsI_by_rqDown oidx msgs.

      split.
      { solve_AtomicInv_rqDown_rsUp.
        { simpl in *; inv H17; mred.
          simpl; intuition solve_msi.
        }
        { simpl in *; inv H17; mred.
          disc_MsgConflictsInv oidx0.
          disc_InvExcl oidx0.
          eapply ObjsInvalid_downRsIM; eauto.
          { apply tl_In; assumption. }
          { assumption. }
        }
      }

      { case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { split_InvDirInv_apply.
            { solve_ObjsInvalid_trivial. }
            { exfalso; disc_dir.
              rewrite getDir_st_I in H20 by assumption.
              solve_msi.
            }
          }
        }
        { disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            disc_MsgConflictsInv oidx.
            solve_by_ObjsInvalid_status_false oidx.
          }
          { case_InvObjOwned.
            { solve_by_ObjsInvalid_status_false oidx. }
            { disc_ObjsInvalid_by oidx0.
              case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
            }
            { solve_MsgsP. }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx.
              { solve_by_ObjsInvalid_status_false oidx. }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx.
              { solve_ObjsInvalid_trivial. }
              { solve_by_ObjsInvalid_status_false oidx. }
            }
          }
        }
      }
    }

    { (* [liDownIRqDownDownDirS] *)
      disc_rule_conds_ex; split.
      { solve_AtomicInv_rqDown_rqDowns.
        { apply Forall_forall; intros.
          apply in_map_iff in H14; dest; subst.
          apply in_map_iff in H17; dest; subst.
          apply H25 in H17.
          apply subtreeChildrenIndsOf_parentIdxOf in H17; auto.
          derive_child_chns x.
          eauto.
        }
        { apply Forall_forall; intros.
          apply in_map_iff in H14; dest; subst.
          repeat constructor; try (red; simpl; intros; intuition discriminate).
        }
      }
      { solve_InvExcl_trivial. }
    }

    { (* [liDownIRqDownDownDirM] *)
      disc_rule_conds_ex; split.
      { solve_AtomicInv_rqDown_rqDowns.
        remember (dir_excl _) as cidx; clear Heqcidx.
        apply subtreeChildrenIndsOf_parentIdxOf in H23; auto.
        derive_child_chns cidx.
        repeat constructor; simpl; eauto.
      }
      { solve_InvExcl_trivial. }
    }

    { (* [liDownIRqDownDownDirMS] *)
      disc_rule_conds_ex; split.
      { solve_AtomicInv_rqDown_rqDowns.
        { apply Forall_forall; intros.
          apply in_map_iff in H14; dest; subst.
          apply in_map_iff in H17; dest; subst.
          apply H25 in H17.
          apply subtreeChildrenIndsOf_parentIdxOf in H17; auto.
          derive_child_chns x.
          eauto.
        }
        { apply Forall_forall; intros.
          apply in_map_iff in H14; dest; subst.
          repeat constructor; try (red; simpl; intros; intuition discriminate).
        }
      }
      { solve_InvExcl_trivial. }
    }

    { (* [liDownIRsUpUpS] *)
      disc_rule_conds_ex.
      disc_MsiDownLockInv oidx Hdlinv.
      derive_footprint_info_basis oidx; [solve_midx_false|].

      (** 1) Each RsUp message is from a child *)
      assert (Forall
                (fun midx =>
                   exists rcidx,
                     parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx /\
                     midx = rsUpFrom rcidx)
                (idsOf rins)) as Hrss.
      { apply Forall_forall; intros rsUp ?.
        eapply RqRsDownMatch_rs_rq in H33; [|rewrite <-H13; eassumption].
        destruct H33 as [cidx [down ?]]; dest.
        derive_child_chns cidx; repeat disc_rule_minds.
        eauto.
      }

      (** 2-1) Each child either sent RsUp or is in DirI *)
      assert (forall rcidx,
                 parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx ->
                 if in_dec idx_dec (rsUpFrom rcidx) (idsOf rins)
                 then True
                 else getDir rcidx os#[dir] = msiI) as Hcs.
      { intros.
        destruct (in_dec idx_dec rcidx (dir_sharers (fst (snd (snd (snd os)))))).
        { find_if_inside; [auto|].
          elim n; rewrite H13, H29; apply in_map; assumption.
        }
        { find_if_inside; [auto|apply getDir_S_non_sharer; assumption]. }
      }

      (** 2-2) Each child subtree satisfies [ObjsInvalid] *)
      assert (forall rcidx,
                 parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx ->
                 forall nost rsTo,
                   ObjsInvalid
                     (fun idx =>
                        In idx (subtreeIndsOf (fst (tree2Topo tr 0)) rcidx))
                     (oss +[oidx <- nost])
                     (enqMP (rsUpFrom oidx) rsTo (deqMsgs (idsOf rins) msgs))) as Hcsi.
      { intros.
        specialize (Hcs _ H31); find_if_inside.
        { apply in_map_iff in i; destruct i as [[midx rs] ?]; simpl in *; dest; subst.
          rewrite Forall_forall in H14; specialize (H14 _ H34).
          rewrite Forall_forall in H23; specialize (H23 _ H34); simpl in *.
          pose proof (H3 _ H34) as Hrein.
          disc_AtomicMsgOutsInv rcidx.
          specialize (H37 eq_refl H23 H14); dest.
          derive_child_st rcidx.
          disc_MsgConflictsInv rcidx.
          rewrite H43 in H37; simpl in H37; dest.
          solve_ObjsInvalid_trivial.
          eapply ObjsInvalid_this_rsUps_deqMsgs_silent; eauto.
          apply parent_not_in_subtree; auto.
        }
        { disc_InvExcl oidx.
          specialize (H34 (tl_In _ _ H8)).
          move H34 at bottom.
          specialize (H34 _ H31); destruct H34 as [? _].
          specialize (H34 Hcs).
          solve_ObjsInvalid_trivial.
          eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
          intro; solve_by_topo_false.
        }
      }

      (** 2-3) The target object itself gets invalid *)
      assert (ObjInvalid0
                oidx (fst os,
                      (false,
                       (invalidate (fst (snd (snd os))),
                        (setDirI, snd (snd (snd (snd os)))))))
                (enqMP (rsUpFrom oidx) {| msg_id := msiDownRsIS;
                                          msg_type := MRs;
                                          msg_addr := msg_addr msg;
                                          msg_value := 0 |}
                       (deqMsgs (idsOf rins) msgs))) as Hoi.
      { intros; repeat split; [simpl; solve_msi|discriminate|].
        clear Hpmcf; preveal Hnmcf.
        assert ((orqs +[oidx <- porq -[downRq]])@[oidx] = Some (porq -[downRq]))
          by mred.
        disc_MsgConflictsInv oidx.
        rewrite H13.
        eapply NoCohMsgs_rsUp_in; eauto.
        { apply InMP_or_enqMP; left; auto. }
        { discriminate. }
        { discriminate. }
      }

      (** 3) Predicate for [msiDownRsIS] *)
      assert (ObjsInvalid
                (fun idx => In idx (subtreeIndsOf (fst (tree2Topo tr 0)) oidx))
                (oss +[oidx <- (fst os,
                                (false,
                                 (invalidate (fst (snd (snd os))),
                                  (setDirI, snd (snd (snd (snd os)))))))])
                (enqMP (rsUpFrom oidx) {| msg_id := msiDownRsIS;
                                          msg_type := MRs;
                                          msg_addr := msg_addr msg;
                                          msg_value := 0 |}
                       (deqMsgs (idsOf rins) msgs))) as Hrc.
      { eapply ObjsInvalid_in_composed; [mred|..].
        { left; apply Hoi. }
        { intros; eapply ObjsInvalid_downRsIM_composed; [mred|eauto]. }
      }

      assert (NoRsI oidx msgs) as Hrsi.
      { move Hidir at bottom.
        specialize (Hidir oidx); simpl in Hidir.
        rewrite H15 in Hidir; simpl in Hidir.
        eapply not_MsgExistsSig_MsgsNotExist; intros;
          inv H31; [|dest_in].
        specialize (Hidir (or_intror (or_intror H32))).
        simpl in *; solve_msi.
      }

      split.
      { rewrite <-H13.
        solve_AtomicInv_rsUps_rsUp.
        { simpl in *; inv H31; mred; simpl; intuition solve_msi. }
        { simpl in *; inv H31; apply Hrc. }
      }

      { case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { split_InvDirInv.
            { rewrite <-H13; eapply Hcsi; eauto. }
            { exfalso.
              simpl in H37; rewrite getDir_setDirI in H37.
              solve_msi.
            }
          }
        }

        { disc_InvExcl_others.
          { disc_InvObjExcl0.
            rewrite <-H13 in H35.
            apply ObjExcl0_other_msg_id_deqMsgs_inv in H35; auto.
            2: { eapply Forall_impl; [|apply H14]; simpl; intros.
                 rewrite H36; discriminate.
            }
            specialize (H4 H35); dest.
            exfalso.
            disc_ObjsInvalid_by oidx.
            rewrite H15 in H37; simpl in H37.
            destruct H37.
            { destruct H37 as [? [? ?]]; auto. }
            { eapply NoRsI_MsgExistsSig_InvRs_false; eauto. }
          }

          { red; intros [? ?].
            assert (NoRsI eidx msgs).
            { disc_MsgsP H36.
              rewrite <-H13 in H36; simpl in H36.
              apply MsgsP_other_msg_id_deqMsgs_inv in H36; auto.
              simpl; apply (DisjList_spec_2 idx_dec); intros; dest_in.
              intro; dest_in.
              apply in_map_iff in H37; destruct H37 as [[rmidx rmsg] [? ?]]; simpl in *.
              rewrite Forall_forall in H14; specialize (H14 _ H38); simpl in *.
              rewrite H14 in H37; discriminate.
            }
            specialize (H32 (conj H35 H37)); dest.

            case_in_subtree oidx eidx;
              [|clear Hrc; solve_by_ObjsInvalid_dir_false oidx].
            split.
            { solve_ObjsInvalid_trivial.
              rewrite <-H13.
              eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
            }
            { solve_MsgsP. }
          }

          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx.
              { clear Hrc; solve_by_ObjsInvalid_dir_false oidx. }
              { solve_ObjsInvalid_trivial.
                rewrite <-H13.
                eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
              }
            }
            { case_in_subtree oidx cidx.
              { solve_ObjsInvalid_trivial.
                rewrite <-H13.
                eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
              }
              { clear Hrc; solve_by_ObjsInvalid_dir_false oidx. }
            }
          }
        }
      }
    }

    { (* [liDownIRsUpUpM] *)
      disc_rule_conds_ex.
      disc_MsiDownLockInv oidx Hdlinv.
      derive_footprint_info_basis oidx; [solve_midx_false|].

      destruct H27; [solve_msi; fail|simpl in *; dest].
      rewrite H30 in *; simpl in *; disc_rule_conds.

      (** 1) Each RsUp message is from a child *)
      assert (Forall
                (fun midx =>
                   exists rcidx,
                     parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx /\
                     midx = rsUpFrom rcidx)
                (map fst (rqi_rss rqi))) as Hrss.
      { apply Forall_forall; intros rsUp ?.
        eapply RqRsDownMatch_rs_rq in H31; [|eassumption].
        destruct H31 as [cidx [down ?]]; dest.
        derive_child_chns cidx; repeat disc_rule_minds.
        eauto.
      }

      (** 2-1) Each child either sent RsUp or is in DirI *)
      assert (forall rcidx,
                 parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx ->
                 if in_dec idx_dec (rsUpFrom rcidx) (map fst (rqi_rss rqi))
                 then True
                 else getDir rcidx os#[dir] = msiI) as Hcs.
      { intros.
        find_if_inside; [auto|].
        rewrite H30 in n.
        eapply getDir_excl_neq; eauto.
        intro Hx; subst.
        elim n; left; reflexivity.
      }

      remember (dir_excl _) as ecidx; clear Heqecidx.
      apply subtreeChildrenIndsOf_parentIdxOf in H29; auto.

      (** 2-2) Each child subtree satisfies [ObjsInvalid] *)
      assert (forall rcidx,
                 parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx ->
                 forall nost rsTo,
                   ObjsInvalid
                     (fun idx =>
                        In idx (subtreeIndsOf (fst (tree2Topo tr 0)) rcidx))
                     (oss +[oidx <- nost])
                     (enqMP (rsUpFrom oidx) rsTo (deqMP (rsUpFrom ecidx) msgs)))
        as Hcsi.
      { intros.
        specialize (Hcs _ H14); find_if_inside.
        { rewrite H30 in i; dest_in; inv H17.
          disc_AtomicMsgOutsInv rcidx.
          specialize (H37 eq_refl H33 H32); dest.
          derive_child_st rcidx.
          disc_MsgConflictsInv rcidx.
          rewrite H42 in H37; simpl in H37; dest.
          solve_ObjsInvalid_trivial.

          eapply ObjsInvalid_in_composed; eauto.
          { left; repeat split; [simpl; solve_msi|intro Hx; simpl in Hx; solve_msi|].
            eapply NoCohMsgs_rsUp_deq; eauto.
          }
          { eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (rminds := [_]); eauto.
            intro Hx; destruct Hx as [ccidx [? ?]].
            eapply subtreeIndsOf_child_SubList in H53; eauto.
            eapply parent_not_in_subtree in H53; eauto.
          }
        }
        { disc_InvExcl oidx.
          specialize (H34 (tl_In _ _ H8)).
          move H34 at bottom.
          specialize (H34 _ H14); destruct H34 as [? _].
          specialize (H34 Hcs).
          solve_ObjsInvalid_trivial.
          eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx) (rminds:= [_]); eauto.
          intro; solve_by_topo_false.
        }
      }

      (** 3) Predicate for [msiDownRsIM] *)
      assert (forall nost rsTo,
                 ObjsInvalid
                   (fun idx =>
                      exists cidx,
                        parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx /\
                        In idx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx))
                   (oss +[oidx <- nost])
                   (enqMP (rsUpFrom oidx) rsTo (deqMP (rsUpFrom ecidx) msgs))) as Hrc.
      { intros; eapply ObjsInvalid_downRsIM_composed; [mred|eauto]. }

      split.
      { solve_AtomicInv_rsUps_rsUp.
        { simpl in *; inv H14; mred; simpl; intuition solve_msi. }
        { simpl in *; inv H14; apply Hrc. }
      }

      { case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { split_InvDirInv.
            { eapply Hcsi; eauto. }
            { exfalso.
              simpl in H37; rewrite getDir_setDirI in H37.
              solve_msi.
            }
          }
        }

        { pose proof Hpmcf as Hpmcf'; phide Hpmcf'; rename H14 into Hpmcf'.
          disc_MsgConflictsInv oidx.

          (* discharge all predicates in [Forall] *)
          derive_child_chns ecidx; repeat disc_rule_minds.
          (* derive the predicate message for it *)
          disc_AtomicMsgOutsInv ecidx.

          derive_child_st ecidx.
          disc_MsgPred.
          preveal Hpmcf'; disc_MsgConflictsInv ecidx.

          disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            exfalso.
            case_idx_eq eidx ecidx.
            { disc_rule_conds; disc_ObjExcl0; solve_msi. }
            { solve_by_ObjsInvalid_downRsIM_false ecidx. }
          }
          { disc_InvObjOwned.
            case_in_subtree ecidx eidx; [|solve_by_ObjsInvalid_downRsIM_false ecidx].
            case_idx_eq eidx ecidx; [disc_rule_conds_ex; congruence|].
            split.
            { assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) eidx)).
              { eapply inside_parent_in with (cidx:= ecidx); eauto. }
              solve_ObjsInvalid_trivial.
            }
            { solve_MsgsP. }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx.
              { assert (In ecidx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx)).
                { eapply inside_child_in; eauto. }
                solve_by_ObjsInvalid_downRsIM_false ecidx.
              }
              { case_in_subtree ecidx cidx; [solve_by_ObjsInvalid_downRsIM_false ecidx|].
                solve_ObjsInvalid_trivial.
              }
            }
            { case_in_subtree ecidx cidx;
                [|solve_by_ObjsInvalid_downRsIM_false ecidx].
              case_idx_eq ecidx cidx; [disc_rule_conds|].
              assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx)).
              { eapply inside_parent_in with (cidx:= ecidx); eauto. }
              solve_ObjsInvalid_trivial.
            }
          }
        }
      }
    }

    { (* [liDownIRsUpUpMS] *)
      disc_rule_conds_ex.
      disc_MsiDownLockInv oidx Hdlinv.
      derive_footprint_info_basis oidx; [solve_midx_false|].
      destruct H27; [simpl in *; dest|solve_msi; fail].

      (** 1) Each RsUp message is from a child *)
      assert (Forall
                (fun midx =>
                   exists rcidx,
                     parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx /\
                     midx = rsUpFrom rcidx)
                (map fst (rqi_rss rqi))) as Hrss.
      { apply Forall_forall; intros rsUp ?.
        eapply RqRsDownMatch_rs_rq in H31; [|eassumption].
        destruct H31 as [cidx [down ?]]; dest.
        derive_child_chns cidx; repeat disc_rule_minds.
        eauto.
      }

      (** 2-1) Each child either sent RsUp or is in DirI *)
      assert (forall rcidx,
                 parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx ->
                 if in_dec idx_dec (rsUpFrom rcidx) (map fst (rqi_rss rqi))
                 then True
                 else getDir rcidx os#[dir] = msiI) as Hcs.
      { intros.
        destruct (in_dec idx_dec rcidx (dir_sharers (fst (snd (snd (snd os)))))).
        { find_if_inside; [auto|].
          elim n; rewrite H30; apply in_map; assumption.
        }
        { find_if_inside; [auto|].
          apply getDir_S_non_sharer; [assumption|].
          intro Hx; elim n; assumption.
        }
      }

      (** 2-2) Each child subtree satisfies [ObjsInvalid] *)
      assert (forall rcidx,
                 parentIdxOf (fst (tree2Topo tr 0)) rcidx = Some oidx ->
                 forall nost rsTo,
                   ObjsInvalid
                     (fun idx =>
                        In idx (subtreeIndsOf (fst (tree2Topo tr 0)) rcidx))
                     (oss +[oidx <- nost])
                     (enqMP (rsUpFrom oidx) rsTo (deqMsgs (map fst (rqi_rss rqi)) msgs))) as Hcsi.
      { rewrite <-H13 in *; intros.
        specialize (Hcs _ H32); find_if_inside.
        { apply in_map_iff in i; destruct i as [[midx rs] ?]; simpl in *; dest; subst.
          rewrite Forall_forall in H14; specialize (H14 _ H34).
          rewrite Forall_forall in H23; specialize (H23 _ H34); simpl in *.
          pose proof (H3 _ H34) as Hrein.
          disc_AtomicMsgOutsInv rcidx.
          specialize (H37 eq_refl H23 H14); dest.
          derive_child_st rcidx.
          disc_MsgConflictsInv rcidx.
          rewrite H43 in H37; simpl in H37; dest.
          solve_ObjsInvalid_trivial.
          eapply ObjsInvalid_this_rsUps_deqMsgs_silent; eauto.
          apply parent_not_in_subtree; auto.
        }
        { disc_InvExcl oidx.
          specialize (H34 (tl_In _ _ H8)).
          move H34 at bottom.
          specialize (H34 _ H32); destruct H34 as [? _].
          specialize (H34 Hcs).
          solve_ObjsInvalid_trivial.
          eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
          intro; solve_by_topo_false.
        }
      }

      (** 3) Predicate for [msiDownRsIM] *)
      assert (forall nost rsTo,
                 ObjsInvalid
                   (fun idx =>
                      exists cidx,
                        parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx /\
                        In idx (subtreeIndsOf (fst (tree2Topo tr 0)) cidx))
                   (oss +[oidx <- nost])
                   (enqMP (rsUpFrom oidx) rsTo
                          (deqMsgs (map fst (rqi_rss rqi)) msgs))) as Hrc.
      { intros; eapply ObjsInvalid_downRsIM_composed; [mred|auto]. }

      assert (NoRsI oidx msgs) as Hrsi.
      { move Hidir at bottom.
        specialize (Hidir oidx); simpl in Hidir.
        rewrite H15 in Hidir; simpl in Hidir.
        eapply not_MsgExistsSig_MsgsNotExist; intros;
          inv H32; [|dest_in].
        specialize (Hidir (or_intror (or_intror H33))).
        simpl in *; solve_msi.
      }

      split.
      { rewrite <-H13.
        solve_AtomicInv_rsUps_rsUp.
        { simpl in *; inv H32; mred; simpl; intuition solve_msi. }
        { simpl in *; inv H32.
          rewrite H13; apply Hrc.
        }
      }

      { case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { split_InvDirInv.
            { eapply Hcsi; eauto. }
            { exfalso.
              simpl in H37; rewrite getDir_setDirI in H37.
              solve_msi.
            }
          }
        }


        { disc_InvExcl_others.
          { disc_InvObjExcl0.
            rewrite <-H13 in H35.
            apply ObjExcl0_other_msg_id_deqMsgs_inv in H35; auto.
            2: { eapply Forall_impl; [|apply H14]; simpl; intros.
                 rewrite H36; discriminate.
            }
            specialize (H4 H35); dest.
            exfalso.
            disc_ObjsInvalid_by oidx.
            rewrite H15 in H37; simpl in H37.
            destruct H37.
            { destruct H37 as [? [? ?]]; auto. }
            { eapply NoRsI_MsgExistsSig_InvRs_false; eauto. }
          }

          { red; intros [? ?].
            assert (NoRsI eidx msgs).
            { disc_MsgsP H36.
              rewrite <-H13 in H36; simpl in H36.
              apply MsgsP_other_msg_id_deqMsgs_inv in H36; auto.
              simpl; apply (DisjList_spec_2 idx_dec); intros; dest_in.
              intro; dest_in.
              apply in_map_iff in H37; destruct H37 as [[rmidx rmsg] [? ?]]; simpl in *.
              rewrite Forall_forall in H14; specialize (H14 _ H38); simpl in *.
              rewrite H14 in H37; discriminate.
            }
            specialize (H33 (conj H35 H37)); dest.

            case_in_subtree oidx eidx;
              [|clear Hrc; solve_by_ObjsInvalid_dir_false oidx].
            split.
            { solve_ObjsInvalid_trivial.
              eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
            }
            { solve_MsgsP. }
          }

          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx.
              { clear Hrc; solve_by_ObjsInvalid_dir_false oidx. }
              { solve_ObjsInvalid_trivial.
                eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
              }
            }
            { case_in_subtree oidx cidx.
              { solve_ObjsInvalid_trivial.
                eapply ObjsInvalid_this_rsUps_deqMsgs_silent with (pidx:= oidx); eauto.
              }
              { clear Hrc; solve_by_ObjsInvalid_dir_false oidx. }
            }
          }
        }
      }
    }

    { (* [liInvRqUpUp] *)
      disc_rule_conds_ex; split.
      { exfalso; destruct rins; [auto|discriminate]. }
      { solve_InvExcl_trivial. }
    }

    { (* [liInvRqUpUpWB] *)
      disc_rule_conds_ex; split.
      { exfalso; destruct rins; [auto|discriminate]. }
      { solve_InvExcl_trivial. }
    }

    { (* [liInvRsDownDown] *)
      disc_rule_conds_ex.
      derive_footprint_info_basis oidx.
      disc_MsgConflictsInv oidx.

      assert (os#[dir].(dir_st) = msiI) as Hdir.
      { move Hidir at bottom.
        specialize (Hidir oidx); simpl in Hidir.
        rewrite H15 in Hidir; simpl in Hidir.
        apply Hidir.
        do 2 right.
        exists (downTo oidx, rmsg); split.
        { apply FirstMP_InMP; assumption. }
        { unfold sigOf; simpl; congruence. }
      }

      split.
      { solve_AtomicInv_rsDown. }
      { case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { split_InvDirInv_apply.
            { solve_ObjsInvalid_trivial. }
            { eapply ObjsInvalid_invRs; eauto.
              apply parent_not_in_subtree; auto.
            }
          }
        }

        { disc_InvExcl_others.
          { disc_InvObjExcl0_apply; split.
            { eapply ObjsInvalid_invRs; eauto. }
            { solve_MsgsP. }
          }
          { case_InvObjOwned.
            { left.
              red; simpl; repeat split; [solve_msi|rewrite Hdir; discriminate|].
              eapply NoCohMsgs_rsDown_deq; eauto.
            }
            { disc_ObjsInvalid_by oidx0.
              case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
            }
            { solve_MsgsP. }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx.
              { eapply ObjsInvalid_invRs; eauto. }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx.
              { solve_ObjsInvalid_trivial. }
              { eapply ObjsInvalid_invRs; eauto. }
            }
          }
        }
      }
    }

    { (* [liPushImm] *)
      disc_rule_conds_ex; split.
      { exfalso; destruct rins; [auto|discriminate]. }
      { eapply InvExcl_state_transition_sound with (porqs:= orqs);
          try eassumption.
        { simpl; intuition solve_msi. }
        { simpl; intuition. }
        { reflexivity. }
      }
    }

    Unshelve.
    all: assumption.

    END_SKIP_PROOF_ON *) admit.
  Qed.

  Lemma msi_InvExcl_InvTrs_l1:
    forall ist1,
      Reachable (steps step_m) impl ist1 ->
      forall inits,
        SubList (idsOf inits) (sys_merqs impl) ->
        forall ins hst outs eouts oidx ridx rins routs,
          Atomic inits ins hst outs eouts ->
          rins <> nil ->
          SubList rins eouts ->
          forall (Hrsd: forall (oidx : IdxT) (rsDown : Id Msg),
                     In rsDown (removeL (id_dec msg_dec) eouts rins ++ routs) ->
                     RsDownMsgTo topo oidx rsDown ->
                     removeL (id_dec msg_dec) eouts rins ++ routs = [rsDown])
                 st2 ist2,
            InvExcl topo cifc st2 ->
            AtomicInv InvExclMsgOutPred inits ist1 hst eouts st2 ->
            steps step_m impl ist1 hst st2 ->
            step_m impl st2 (RlblInt oidx ridx rins routs) ist2 ->
            forall (Hr1: Reachable (steps step_m) impl st2)
                   (Hr2: Reachable (steps step_m) impl ist2)
                   (Hoin: In oidx (map obj_idx (map l1 (c_l1_indices (snd (tree2Topo tr 0)))))),
              AtomicInv InvExclMsgOutPred inits ist1 (RlblInt oidx ridx rins routs :: hst)
                        (removeL (id_dec msg_dec) eouts rins ++ routs) ist2 /\
              InvExcl topo cifc ist2.
  Proof. (* SKIP_PROOF_ON
    intros.
    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    pose proof (footprints_ok
                  (msi_GoodORqsInit Htr)
                  (msi_GoodRqRsSys Htr) Hr1) as Hftinv.
    pose proof (msi_InvL1DirI_ok Hr1) as Hdiri.
    pose proof (msi_InObjInds Hr1) as Hioi1.
    pose proof (msi_InObjInds Hr2) as Hioi2.
    pose proof (msi_OstInds Hr1) as Hosi.
    pose proof (msi_MsgConflictsInv
                  (@msi_RootChnInv_ok _ Htr) Hr1) as Hpmcf.
    pose proof (@MsiUpLockInv_ok _ Htr _ Hr1) as Hulinv.
    pose proof (@MsiDownLockInv_ok _ Htr _ Hr1) as Hdlinv.

    inv_step.

    simpl in H12; destruct H12; [subst|apply in_app_or in H7; destruct H7].
    1: {
      exfalso; simpl in Hoin.
      rewrite map_map in Hoin; simpl in Hoin; rewrite map_id in Hoin.
      eapply tree2Topo_root_not_in_l1; eauto.
    }
    1: {
      exfalso; simpl in Hoin.
      apply in_map_iff in H7; destruct H7 as [oidx [? ?]]; subst.
      rewrite map_map in Hoin; simpl in Hoin; rewrite map_id in Hoin.
      pose proof (tree2Topo_WfCIfc tr 0) as [? _].
      apply (DisjList_NoDup idx_dec) in H7.
      eapply DisjList_In_1; eauto.
      apply tl_In; assumption.
    }

    (*! Cases for L1 caches *)
    apply in_map_iff in H7; destruct H7 as [oidx [? ?]]; subst.

    pose proof (c_l1_indices_has_parent Htr _ _ H8).
    destruct H7 as [pidx [? ?]].
    pose proof (Htn _ _ H9); dest.

    (** The object index does not belong to [c_li_indices]. *)
    assert (~ In oidx (c_li_indices (snd (tree2Topo tr 0)))) as Hnli.
    { pose proof (tree2Topo_WfCIfc tr 0) as [? _].
      apply (DisjList_NoDup idx_dec) in H14.
      eapply DisjList_In_1; eassumption.
    }

    (** Do case analysis per a rule. *)
    dest_in.

    { (* [l1GetSImm] *)
      disc_rule_conds_ex; exfalso; disc_AtomicMsgOutsInv (l1ExtOf oidx); eauto.
    }

    { (* [l1GetSRqUpUp] *)
      disc_rule_conds_ex; exfalso; disc_AtomicMsgOutsInv (l1ExtOf oidx); eauto.
    }

    { (* [l1GetSRsDownDownS] *)
      disc_rule_conds_ex.
      derive_footprint_info_basis oidx.
      derive_child_chns cidx.
      disc_rule_conds_ex.

      split.
      { solve_AtomicInv_rsDown. }
      { solve_InvExcl_trivial.
        case_InvExcl_me_others.
        { disc_InvExcl_this; [solve_InvObjExcl0_by_ObjExcl0_false| |].
          { case_InvObjOwned.
            { solve_by_topo_false. }
            { disc_ObjsInvalid_by oidx0.
              case_ObjInvalid_with (l1ExtOf oidx).
              { solve_by_topo_false. }
              { case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs]. }
            }
            { solve_MsgsP. }
          }
          { red; intros; exfalso; auto. }
        }

        { disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            disc_MsgConflictsInv oidx.
            solve_by_ObjsInvalid_rsS_false oidx.
          }
          { case_InvObjOwned.
            { disc_MsgConflictsInv oidx.
              solve_by_ObjsInvalid_rsS_false oidx.
            }
            { disc_ObjsInvalid_by oidx0.
              case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
            }
            { solve_MsgsP. }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx.
              { disc_MsgConflictsInv oidx.
                solve_by_ObjsInvalid_rsS_false oidx.
              }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx.
              { solve_ObjsInvalid_trivial. }
              { disc_MsgConflictsInv oidx.
                solve_by_ObjsInvalid_rsS_false oidx.
              }
            }
          }
        }
      }
    }

    { (* [l1DownSImm] *)
      disc_rule_conds_ex.
      derive_NoRsI_by_rqDown oidx msgs.

      split.
      { solve_AtomicInv_rqDown_rsUp.
        solve_DownRsSPred.
      }
      { case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { red; intros; exfalso; auto. }
        }
        { disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            solve_by_ObjsInvalid_status_false oidx.
          }
          { case_InvObjOwned.
            { solve_by_ObjsInvalid_status_false oidx. }
            { disc_ObjsInvalid_by oidx0.
              case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
            }
            { solve_MsgsP. }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx.
              { solve_by_ObjsInvalid_status_false oidx. }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx.
              { solve_ObjsInvalid_trivial. }
              { solve_by_ObjsInvalid_status_false oidx. }
            }
          }
        }
      }
    }

    { (* [l1GetMImmM] *)
      disc_rule_conds_ex; exfalso; disc_AtomicMsgOutsInv (l1ExtOf oidx); eauto.
    }

    { (* [l1GetMRqUpUp] *)
      disc_rule_conds_ex; exfalso; disc_AtomicMsgOutsInv (l1ExtOf oidx); eauto.
    }

    { (* [l1GetMRsDownDown] *)
      disc_rule_conds_ex.
      derive_footprint_info_basis oidx.
      derive_child_chns cidx.
      disc_rule_conds_ex.
      derive_NoRsI_by_rsDown oidx msgs.

      split.
      { solve_AtomicInv_rsDown. }
      { disc_MsgConflictsInv oidx.
        solve_InvExcl_trivial.
        disc_AtomicMsgOutsInv oidx.
        disc_MsgPred.

        case_InvExcl_me_others.
        { disc_InvExcl_this.
          { red; intros; split.
            { solve_ObjsInvalid_trivial. }
            { eapply NoCohMsgs_rsDown_deq; eauto. }
          }
          { disc_InvObjOwned; split.
            { solve_ObjsInvalid_trivial. }
            { eapply NoCohMsgs_rsDown_deq; eauto. }
          }
          { red; intros; exfalso; auto. }
        }

        { apply ObjsInvalid_shrinked in H39; [|eassumption..].
          disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            disc_ObjExcl0.
            clear H4; solve_by_ObjsInvalid_status_false eidx.
          }
          { case_InvObjOwned.
            { disc_MsgConflictsInv oidx.
              solve_by_ObjsInvalid_rsM_false oidx.
            }
            { disc_ObjsInvalid_by oidx0.
              case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
            }
            { solve_MsgsP. }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx.
              { disc_MsgConflictsInv oidx.
                solve_by_ObjsInvalid_rsM_false oidx.
              }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx.
              { solve_ObjsInvalid_trivial. }
              { disc_MsgConflictsInv oidx.
                solve_by_ObjsInvalid_rsM_false oidx.
              }
            }
          }
        }
      }
    }

    { (* [l1DownIImmS] *)
      disc_rule_conds_ex.
      derive_NoRsI_by_rqDown oidx msgs.

      split.
      { disc_MsgConflictsInv oidx.
        solve_AtomicInv_rqDown_rsUp.
        { simpl in *; inv H31; mred.
          simpl; intuition solve_msi.
        }
        { simpl in *; inv H31; mred.
          eapply ObjsInvalid_in_composed; [mred|..].
          { left; repeat split; [simpl; solve_msi|..].
            { Ltac disc_InvL1DirI oidx :=
                match goal with
                | [Hdiri: InvL1DirI _ _, Hin: In oidx (c_l1_indices _), Host: _@[oidx] = Some _
                   |- _] =>
                  red in Hdiri; rewrite Forall_forall in Hdiri; specialize (Hdiri _ Hin);
                  simpl in Hdiri; rewrite Host in Hdiri; simpl in Hdiri
                end.
                disc_InvL1DirI oidx0.
                simpl; rewrite Hdiri; discriminate.
            }
            { apply NoCohMsgs_enq; [|solve_not_in].
              eapply NoCohMsgs_rqDown_deq; eauto.
            }
          }
          { eapply ObjsInvalid_l1_singleton; eauto; mred. }
        }
      }

      { case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { red; intros; exfalso; auto. }
        }
        { disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            split; [|solve_MsgsP].
            solve_ObjsInvalid_trivial.
            eapply ObjsInvalid_state_transition_sound; eauto.
            simpl; solve_msi.
          }
          { disc_InvObjOwned.
            split; [|solve_MsgsP].
            solve_ObjsInvalid_trivial.
            eapply ObjsInvalid_state_transition_sound; eauto.
            simpl; solve_msi.
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx.
              { solve_ObjsInvalid_trivial.
                eapply ObjsInvalid_state_transition_sound; eauto.
                simpl; solve_msi.
              }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx.
              { solve_ObjsInvalid_trivial. }
              { solve_ObjsInvalid_trivial.
                eapply ObjsInvalid_state_transition_sound; eauto.
                simpl; solve_msi.
              }
            }
          }
        }
      }
    }

    { (* [l1DownIImmM] *)
      disc_rule_conds_ex.
      derive_NoRsI_by_rqDown oidx msgs.

      split.
      { disc_MsgConflictsInv oidx.
        solve_AtomicInv_rqDown_rsUp.
        { simpl in *; inv H31; mred; simpl.
          repeat split.
          { solve_msi. }
          { disc_InvL1DirI oidx0; assumption. }
        }
        { simpl in *; inv H31; mred.
          eapply ObjsInvalid_l1_singleton; eauto; mred.
        }
      }
      { case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { red; intros; exfalso; auto. }
        }
        { disc_InvExcl_others.
          { disc_InvObjExcl0_apply.
            solve_by_ObjsInvalid_status_false oidx.
          }
          { case_InvObjOwned.
            { solve_by_ObjsInvalid_status_false oidx. }
            { disc_ObjsInvalid_by oidx0.
              case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
            }
            { solve_MsgsP. }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx.
              { solve_by_ObjsInvalid_status_false oidx. }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx.
              { solve_ObjsInvalid_trivial. }
              { solve_by_ObjsInvalid_status_false oidx. }
            }
          }
        }
      }
    }

    { (* [l1InvRqUpUp] *)
      disc_rule_conds_ex; exfalso; destruct rins; [auto|discriminate].
    }

    { (* [l1InvRqUpUpWB] *)
      disc_rule_conds_ex; exfalso; destruct rins; [auto|discriminate].
    }

    { (* [l1InvRsDownDown] *)
      disc_rule_conds_ex.
      derive_footprint_info_basis oidx.
      disc_InvL1DirI oidx.

      split.
      { solve_AtomicInv_rsDown. }
      { case_InvExcl_me_others.
        { disc_InvExcl_this.
          { solve_InvObjExcl0_by_ObjExcl0_false. }
          { solve_InvObjOwned_by_false. }
          { red; intros; exfalso; auto. }
        }

        { disc_MsgConflictsInv oidx.
          disc_InvExcl_others.
          { disc_InvObjExcl0_apply; split.
            { eapply ObjsInvalid_invRs; eauto. }
            { solve_MsgsP. }
          }
          { case_InvObjOwned.
            { left.
              red; simpl; repeat split; [solve_msi| |].
              { simpl; rewrite Hdiri; discriminate. }
              { eapply NoCohMsgs_rsDown_deq; eauto. }
            }
            { disc_ObjsInvalid_by oidx0.
              case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
            }
            { solve_MsgsP. }
          }
          { split_InvDirInv_apply.
            { case_in_subtree oidx cidx.
              { eapply ObjsInvalid_invRs; eauto. }
              { solve_ObjsInvalid_trivial. }
            }
            { case_in_subtree oidx cidx.
              { solve_ObjsInvalid_trivial. }
              { eapply ObjsInvalid_invRs; eauto. }
            }
          }
        }
      }
    }

    END_SKIP_PROOF_ON *) admit.
  Qed.

  Lemma msi_InvExcl_InvTrs: InvTrs impl (InvExcl topo cifc).
  Proof.
    eapply inv_atomic_InvTrs;
      [red; intros; eapply msi_InvExcl_InvTrsIns; eauto
      |red; intros; eapply msi_InvExcl_InvTrsOuts; eauto
      |].
    instantiate (1:= AtomicInv InvExclMsgOutPred).

    red; intros.
    destruct H1.
    generalize dependent ist2.

    induction H3; simpl; intros; subst;
      [inv_steps; apply msi_InvExcl_InvTrs_init; auto|].

    assert (Atomic inits (ins ++ rins) (RlblInt oidx ridx rins routs :: hst)
                   (outs ++ routs) (removeL (id_dec msg_dec) eouts rins ++ routs)) as Hnatm
        by (econstructor; eauto).
    pose proof (atomic_rsDown_singleton
                  (msi_GoodORqsInit Htr)
                  (msi_RqRsSys Htr)
                  Hnatm H H8) as Hrsd.
    clear Hnatm.

    inv_steps.
    pose proof (reachable_steps H H9) as Hr1.
    pose proof (reachable_steps Hr1 (steps_singleton H11)) as Hr2.
    specialize (IHAtomic H1 _ H9); dest.

    destruct (in_dec idx_dec oidx (map obj_idx (sys_objs impl))) as [Hoin|Hx];
      [|exfalso; inv_step; elim Hx; apply in_map; assumption].
    simpl in Hoin; destruct Hoin as [Hoin|Hoin];
      [|rewrite map_app in Hoin; apply in_app_or in Hoin; destruct Hoin as [Hoin|Hoin]].

    - eapply msi_InvExcl_InvTrs_mem; eauto.
    - eapply msi_InvExcl_InvTrs_li; eauto.
    - eapply msi_InvExcl_InvTrs_l1; eauto.
  Qed.

  Lemma msi_InvExcl_step:
    InvStep impl step_m (InvExcl topo cifc).
  Proof.
    apply invSeq_serializable_invStep.
    - apply msi_InvExcl_init.
    - apply inv_trs_seqSteps.
      apply msi_InvExcl_InvTrs.
    - eapply rqrs_Serializable.
      + apply msi_GoodORqsInit.
      + apply MsiObjInvs_ok.
      + apply msi_RqRsSys.
  Qed.

  Lemma msi_InvExcl_ok:
    Invariant.InvReachable impl step_m (InvExcl topo cifc).
  Proof.
    eapply inv_reachable.
    - typeclasses eauto.
    - apply msi_InvExcl_init.
    - apply msi_InvExcl_step.
  Qed.

End InvExcl.
