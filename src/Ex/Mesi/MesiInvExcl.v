Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLangEx RqRsInvMsg RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Require Import Ex.Mesi.MesiInv.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Local Arguments idx_dec: simpl never.

(** TODO: move to [Mesi/Mesi.v] *)
Ltac dir_crush :=
  cbv [getDir addSharer removeSharer
              setDirI setDirS setDirE setDirM];
  simpl; intros;
  repeat find_if_inside;
  repeat
    (try match goal with
         | [H: ~ In ?oidx (?oidx :: _) |- _] => elim H; left; reflexivity
         | [Ht: In ?oidx ?l, Hn: ~ In ?oidx (_ :: ?l) |- _] => elim Hn; right; assumption
         | [H: In _ (_ :: _) |- _] => inv H
         | [H: _ |- _] => exfalso; auto; fail
         end; try subst; try reflexivity; try assumption; try solve_mesi).

Lemma getDir_addSharer_spec:
  forall dir,
    dir.(dir_st) <= mesiS ->
    forall oidx sidx,
      getDir oidx (addSharer sidx dir) =
      if idx_dec sidx oidx
      then mesiS else getDir oidx dir.
Proof. dir_crush. Qed.

Lemma getDir_st_I:
  forall dir,
    dir.(dir_st) = mesiI ->
    forall oidx, getDir oidx dir = mesiI.
Proof. dir_crush. Qed.
    
Lemma getDir_st_sound:
  forall dir oidx,
    mesiS <= getDir oidx dir ->
    getDir oidx dir <= dir.(dir_st).
Proof. dir_crush. Qed.

Lemma getDir_setDirS_I_imp:
  forall oidx shs, getDir oidx (setDirS shs) = mesiI -> ~ In oidx shs.
Proof. dir_crush. Qed.

Lemma getDir_setDirS_S_imp:
  forall oidx shs, getDir oidx (setDirS shs) = mesiS -> In oidx shs.
Proof. dir_crush. Qed.

Lemma getDir_setDirS_sound:
  forall oidx shs, getDir oidx (setDirS shs) <= mesiS.
Proof. dir_crush. Qed.

Lemma getDir_setDirE_eq:
  forall oidx, getDir oidx (setDirE oidx) = mesiE.
Proof. dir_crush. Qed.

Lemma getDir_setDirE_neq:
  forall oidx eidx, eidx <> oidx -> getDir oidx (setDirE eidx) = mesiI.
Proof. dir_crush. Qed.

Lemma getDir_setDirM_eq:
  forall oidx, getDir oidx (setDirM oidx) = mesiM.
Proof. dir_crush. Qed.

Lemma getDir_setDirM_neq:
  forall oidx eidx, eidx <> oidx -> getDir oidx (setDirM eidx) = mesiI.
Proof. dir_crush. Qed.

Lemma getDir_excl_eq:
  forall dir eidx,
    eidx = dir.(dir_excl) ->
    mesiE <= dir.(dir_st) <= mesiM ->
    getDir eidx dir = dir.(dir_st).
Proof. dir_crush. Qed.

Lemma getDir_excl_neq:
  forall dir eidx,
    eidx = dir.(dir_excl) ->
    mesiE <= dir.(dir_st) <= mesiM ->
    forall oidx,
      oidx <> eidx ->
      getDir oidx dir = mesiI.
Proof. dir_crush. Qed.

(** TODO: move to [Topology.v] *)
Lemma root_not_in_subtree:
  forall dtr (Hwf: WfDTree dtr) oidx,
    oidx <> rootOf dtr ->
    In oidx (indsOf dtr) ->
    ~ In (rootOf dtr) (subtreeIndsOf dtr oidx).
Proof.
  intros; intro Hx.
  erewrite <-subtreeIndsOf_indsOf in H0; [|eassumption|apply Subtree_refl].
  eapply subtreeIndsOf_In_each_other_eq in Hx; eauto.
Qed.
  
Lemma subtreeIndsOf_in_has_parent:
  forall dtr (Hwf: WfDTree dtr) cidx oidx pidx,
    parentIdxOf dtr oidx = Some pidx ->
    In cidx (subtreeIndsOf dtr oidx) ->
    exists cpidx, parentIdxOf dtr cidx = Some cpidx.
Proof.
  intros.
  assert (parentChnsOf cidx dtr <> None).
  { apply indsOf_parentChnsOf_not_None.
    { apply parentIdxOf_child_indsOf in H.
      erewrite <-subtreeIndsOf_indsOf in H; [|eassumption|apply Subtree_refl].
      apply subtreeIndsOf_SubList in H; auto.
      erewrite <-subtreeIndsOf_indsOf; [|eassumption|apply Subtree_refl].
      auto.
    }
    { intro Hx; subst.
      eapply root_not_in_subtree; eauto;
        [|eapply parentIdxOf_child_indsOf; eauto].
      intro Hx; subst.
      apply parentIdxOf_child_not_root in H; auto.
    }
  }
  destruct (parentChnsOf cidx dtr) as [rd|] eqn:Hpchn; [|exfalso; auto].
  unfold parentIdxOf; rewrite Hpchn; simpl; eauto.
Qed.  

Existing Instance Mesi.ImplOStateIfc.

Definition ObjsInvalid (inP: IdxT -> Prop) (oss: OStates) (msgs: MessagePool Msg) :=
  forall oidx,
    inP oidx ->
    ost <+- oss@[oidx]; ObjInvalid oidx ost msgs.

Definition InvObjExcl0 (eidx: IdxT) (ost: OState) (oss: OStates)
           (msgs: MessagePool Msg) :=
  ObjExcl0 eidx ost msgs ->
  ObjsInvalid (fun oidx => eidx <> oidx) oss msgs /\
  NoCohMsgs eidx msgs.

Definition InvObjOwned (topo: DTree) (eidx: IdxT) (eost: OState) (oss: OStates)
           (msgs: MessagePool Msg) :=
  eost#[owned] = true ->
  ObjsInvalid (fun oidx => ~ In oidx (subtreeIndsOf topo eidx)) oss msgs.

Definition InvDirInv (topo: DTree) (cifc: CIfc) (eidx: IdxT) (eost: OState) (oss: OStates)
           (msgs: MessagePool Msg) :=
  In eidx (c_li_indices cifc) ->
  forall cidx,
    parentIdxOf topo cidx = Some eidx ->
    (getDir cidx eost#[dir] = mesiI ->
     ObjsInvalid (fun oidx => In oidx (subtreeIndsOf topo cidx)) oss msgs) /\
    (mesiE <= getDir cidx eost#[dir] ->
     ObjsInvalid (fun oidx => ~ In oidx (subtreeIndsOf topo cidx)) oss msgs).

Definition InvExcl (topo: DTree) (cifc: CIfc) (st: MState): Prop :=
  forall eidx,
    eost <+- (bst_oss st)@[eidx];
      (InvObjExcl0 eidx eost (bst_oss st) (bst_msgs st) /\
       InvObjOwned topo eidx eost (bst_oss st) (bst_msgs st) /\
       InvDirInv topo cifc eidx eost (bst_oss st) (bst_msgs st)).

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
        msg.(msg_id) <> mesiInvRs ->
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
      Forall (fun idm => (valOf idm).(msg_id) <> mesiInvRs) rmsgs ->
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
          mesiS <= ost#[status] ->
          False.
  Proof.
    intros.
    specialize (H _ H0).
    rewrite H2 in H; simpl in H.
    destruct H.
    - red in H; solve_mesi.
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
      destruct H.
      split; [assumption|dest_in; solve_MsgsP].
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
      destruct H.
      split; [assumption|dest_in; solve_MsgsP].
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
          rsdm.(msg_id) = mesiRsS ->
          False.
  Proof.
    intros.
    specialize (H _ H1).
    rewrite H0 in H; simpl in H.
    destruct H.
    - red in H; dest.
      specialize (H6 (downTo oidx, rsdm) H3).
      red in H6; rewrite map_trans, map_cons in H6.
      rewrite caseDec_head_eq in H6
        by (unfold sigOf; simpl; congruence).
      auto.
    - destruct H as [[midx msg] [? ?]]; simpl in *.
      unfold sigOf in H6; simpl in H6; inv H6.
      specialize (H2 (downTo oidx, rsdm) eq_refl H4 H3); dest.
      eapply (H7 (downTo oidx, msg)); eauto.
      simpl; intro Hx; subst.
      rewrite H5 in H10; discriminate.
  Qed.

  Lemma ObjsInvalid_rsE_false:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall oidx ost orq,
        oss@[oidx] = Some ost ->
        inP oidx ->
        RsDownConflicts oidx orq msgs ->
        forall rsdm,
          InMP (downTo oidx) rsdm msgs ->
          rsdm.(msg_type) = MRs ->
          rsdm.(msg_id) = mesiRsE ->
          False.
  Proof.
    intros.
    specialize (H _ H1).
    rewrite H0 in H; simpl in H.
    destruct H.
    - red in H; dest.
      specialize (H6 (downTo oidx, rsdm) H3).
      red in H6; rewrite map_trans, map_cons in H6.
      rewrite caseDec_head_neq in H6
        by (unfold sigOf; simpl; intro Hx; inv Hx;
            rewrite H5 in H9; discriminate).
      rewrite map_cons in H6.
      rewrite caseDec_head_eq in H6
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
          rsdm.(msg_id) = mesiRsM ->
          False.
  Proof.
    intros.
    specialize (H _ H1).
    rewrite H0 in H; simpl in H.
    destruct H.
    - red in H; dest.
      specialize (H6 (downTo oidx, rsdm) H3).
      red in H6; rewrite map_trans, map_cons in H6.
      do 2 (rewrite caseDec_head_neq in H6
             by (unfold sigOf; simpl; intro Hx; inv Hx;
                 rewrite H5 in H9; discriminate);
            rewrite map_cons in H6).
      rewrite caseDec_head_eq in H6
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
          rsum.(msg_id) = mesiDownRsS ->
          False.
  Proof.
    intros.
    specialize (H _ H1).
    rewrite H0 in H; simpl in H.
    destruct H.
    - red in H; dest.
      specialize (H6 (rsUpFrom oidx, rsum) H3).
      red in H6; rewrite map_trans, map_cons in H6.
      do 3 (rewrite caseDec_head_neq in H6
             by (unfold sigOf; simpl; intro Hx; inv Hx;
                 rewrite H5 in H9; discriminate);
            rewrite map_cons in H6).
      rewrite caseDec_head_eq in H6
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
        ~ In msg.(msg_id) [mesiRsS; mesiRsE; mesiRsM; mesiDownRsS] ->
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
    - destruct H5 as [[rsDown rsdm] [? ?]]; inv H5.
      apply InMP_deqMP in H4.
      specialize (H1 (downTo oidx, rsdm) eq_refl H8 H4); dest.
      eapply H10 with (rqDown:= (downTo oidx, rmsg)); eauto.
    - destruct H5 as [[rsDown rsdm] [? ?]]; inv H5.
      apply InMP_deqMP in H4.
      specialize (H1 (downTo oidx, rsdm) eq_refl H8 H4); dest.
      eapply H10 with (rqDown:= (downTo oidx, rmsg)); eauto.
    - destruct H5 as [[rsDown rsdm] [? ?]]; inv H5.
      apply InMP_deqMP in H4.
      specialize (H1 (downTo oidx, rsdm) eq_refl H8 H4); dest.
      eapply H10 with (rqDown:= (downTo oidx, rmsg)); eauto.
    - destruct H5 as [rsUp [? ?]]; inv H5.
      apply H3 with (rsUp:= rsUp); auto.
      eapply InMP_deqMP; eauto.
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
    - destruct H8 as [[midx msg] [? ?]]; inv H8.
      apply H4.
      eapply rssQ_deq_in_length_two; eauto.
    - destruct H8 as [[midx msg] [? ?]]; inv H8.
      apply H4.
      eapply rssQ_deq_in_length_two; eauto.
    - destruct H8 as [[midx msg] [? ?]]; inv H8.
      apply H4.
      eapply rssQ_deq_in_length_two; eauto.
    - destruct H8 as [rsUp [? ?]]; inv H8.
      apply H6 with (rsUp:= rsUp); auto.
      eapply InMP_deqMP; eauto.
  Qed.

  Lemma ObjsInvalid_invRs:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall oidx orq,
        inP oidx ->
        RsDownConflicts oidx orq msgs ->
        forall nost: OState,
          nost#[status] = mesiNP ->
          nost#[owned] = false ->
          forall rmsg,
            FirstMPI msgs (downTo oidx, rmsg) ->
            rmsg.(msg_type) = MRs ->
            ObjsInvalid inP (oss +[ oidx <- nost]) (deqMP (downTo oidx) msgs).
  Proof.
    intros.
    red; intros roidx ?.
    specialize (H _ H6).
    mred; simpl in *; auto.
    - left; split.
      + simpl; solve_mesi.
      + eapply NoCohMsgs_rsDown_deq; eauto.
    - destruct (oss@[roidx]) as [rost|]; simpl in *; auto.
      destruct H; [left|right].
      + destruct H; split; [assumption|].
        solve_MsgsP.
      + destruct H as [[midx msg] [? ?]].
        exists (midx, msg); split; [|assumption]; inv H7.
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

    Lemma ObjsInvalid_l1_singleton:
      forall oss orqs msgs,
        InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
        forall eidx,
          In eidx (c_l1_indices cifc) ->
          forall eost,
            oss@[eidx] = Some eost ->
            ObjInvalid eidx eost msgs ->
            ObjsInvalid (fun oidx => In oidx (subtreeIndsOf topo eidx)) oss msgs.
    Proof.
      intros; subst topo.
      red; intros.
      destruct (oss@[oidx]) as [ost|] eqn:Host; simpl; [|auto].
      rewrite tree2Topo_l1_subtreeIndsOf in H3 by assumption.
      dest_in; [congruence|].
      exfalso.
      specialize (H (l1ExtOf eidx)); simpl in H.
      rewrite Host in H; simpl in H.
      eapply tree2Topo_l1_child_ext_not_in; eauto.
    Qed.

    Lemma ObjsInvalid_rsE:
      forall oss msgs oidx orq,
        ObjsInvalid (fun idx => oidx <> idx) oss msgs ->
        RsDownConflicts oidx orq msgs ->
        forall cidx (nost: OState) rmsg,
          parentIdxOf topo cidx = Some oidx ->
          nost#[status] = mesiI ->
          FirstMPI msgs (downTo oidx, rmsg) ->
          rmsg.(msg_type) = MRs ->
          ObjsInvalid (fun idx => cidx <> idx)
                      (oss +[oidx <- nost])
                      (deqMP (downTo oidx) msgs).
    Proof.
      intros; subst topo.
      red; intros; mred.
      - simpl; left; split; [simpl in *; solve_mesi|].
        eapply NoCohMsgs_rsDown_deq; eauto.
      - specialize (H _ (neq_sym n)).
        destruct (oss@[oidx0]) as [ost|]; simpl in *; auto.
        destruct H; [left|right].
        + destruct H; split; [assumption|].
          solve_MsgsP.
        + destruct H as [[midx msg] [? ?]].
          exists (midx, msg); split; [|assumption]; inv H6.
          apply deqMP_InMP_midx; [assumption|].
          simpl; intro Hx; subst.
          inv Hx; auto.
    Qed.

    Lemma ObjsInvalid_rsM:
      forall oss msgs oidx (ost: OState) orq,
        In oidx (c_li_indices cifc) ->
        ObjsInvalid (fun idx => ~ In idx (subtreeIndsOf topo oidx)) oss msgs ->
        RsDownConflicts oidx orq msgs ->
        ost#[dir].(dir_st) = mesiI ->
        InvDirInv topo cifc oidx ost oss msgs ->
        forall cidx (nost: OState) rmsg,
          nost#[status] = mesiI ->
          FirstMPI msgs (downTo oidx, rmsg) ->
          rmsg.(msg_type) = MRs ->
          ObjsInvalid (fun idx => ~ In idx (subtreeIndsOf topo cidx))
                      (oss +[oidx <- nost])
                      (deqMP (downTo oidx) msgs).
    Proof.
      intros; subst topo.
      red; intros; mred.
      - simpl; left; split; [simpl in *; solve_mesi|].
        eapply NoCohMsgs_rsDown_deq; eauto.
      - destruct (in_dec idx_dec oidx0 (subtreeIndsOf (fst (tree2Topo tr 0)) oidx)).
        + apply subtreeIndsOf_composed in i; auto.
          destruct i; [exfalso; auto|].
          destruct H8 as [rcidx [? ?]].

          (* Discharge [InvDirInv] *)
          specialize (H3 H _ H8); destruct H3 as [? _].
          specialize (H3 (getDir_st_I _ H2 _)).
          specialize (H3 _ H9).

          destruct (oss@[oidx0]) as [ost0|]; simpl in *; auto.
          destruct H3; [left|right].
          * destruct H3; split; [assumption|].
            solve_MsgsP.
          * destruct H3 as [[midx msg] [? ?]].
            exists (midx, msg); split; [|assumption]; inv H10.
            apply deqMP_InMP_midx; [assumption|].
            simpl; intro Hx; subst.
            inv Hx; auto.
          
        + specialize (H0 _ n0).
          destruct (oss@[oidx0]) as [ost0|]; simpl in *; auto.
          destruct H0; [left|right].
          * destruct H0; split; [assumption|].
            solve_MsgsP.
          * destruct H0 as [[midx msg] [? ?]].
            exists (midx, msg); split; [|assumption]; inv H8.
            apply deqMP_InMP_midx; [assumption|].
            simpl; intro Hx; subst.
            inv Hx; auto.
    Qed.

    Lemma ObjsInvalid_downRsI:
      forall oss msgs oidx (ost: OState) orq,
        In oidx (c_li_indices cifc) ->
        RqDownConflicts oidx msgs ->
        RsDownConflicts oidx orq msgs ->
        ost#[dir].(dir_st) = mesiI ->
        InvDirInv topo cifc oidx ost oss msgs ->
        forall (nost: OState) rqm rsm,
          nost#[status] = mesiI ->
          FirstMPI msgs (downTo oidx, rqm) ->
          rqm.(msg_type) = MRq ->
          rsm.(msg_id) = mesiDownRsI ->
          ObjsInvalid (fun idx => In idx (subtreeIndsOf topo oidx))
                      (oss +[oidx <- nost])
                      (enqMP (rsUpFrom oidx) rsm (deqMP (downTo oidx) msgs)).
    Proof.
      intros; subst topo.
      red; intros; mred.
      - simpl; left; split; [simpl in *; solve_mesi|].
        apply NoCohMsgs_enq; [|rewrite H7; solve_not_in].
        eapply NoCohMsgs_rqDown_deq; eauto.
      - destruct (oss@[oidx0]) as [ost0|] eqn:Host; simpl; auto.
        apply subtreeIndsOf_composed in H8; auto.
        destruct H8; [exfalso; auto|].
        destruct H8 as [cidx [? ?]].

        (* Discharge [InvDirInv] *)
        specialize (H3 H _ H8); destruct H3 as [? _].
        specialize (H3 (getDir_st_I _ H2 _)).
        specialize (H3 _ H9).

        rewrite Host in H3; simpl in H3.
        destruct H3; [left|right].
        + destruct H3; split; [assumption|].
          solve_MsgsP.
        + destruct H3 as [[midx msg] [? ?]].
          exists (midx, msg); split; [|assumption]; inv H10.
          apply InMP_or_enqMP; right.
          apply deqMP_InMP_midx; [assumption|].
          simpl; intro Hx; inv Hx; auto.
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
    split; [simpl; solve_mesi|].
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

  Lemma mesi_InvExcl_init:
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
            left; repeat split; [simpl; solve_mesi..|].
            do 3 red; intros; do 2 red in H3; dest_in.
          }
          { rewrite implOStatesInit_None in Host by assumption.
            discriminate.
          }
        * do 3 red; intros; do 2 red in H1; dest_in.
      + exfalso.
        rewrite implOStatesInit_value_non_root in Heost by assumption.
        inv Heost.
        simpl in *; solve_mesi.

    - red; intros.
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
            left; repeat split; [simpl; solve_mesi..|].
            do 3 red; intros; do 2 red in H2; dest_in.
          }
        * rewrite implOStatesInit_None in Host by assumption; discriminate.
      + rewrite implOStatesInit_value_non_root in Heost by assumption.
        inv Heost; discriminate.

    - red; intros.
      destruct (in_dec idx_dec eidx (c_li_indices cifc ++ c_l1_indices cifc));
        [|rewrite implOStatesInit_None in Heost by assumption; discriminate].
      rewrite c_li_indices_head_rootOf in i by assumption; inv i.
      + rewrite implOStatesInit_value_root in Heost by assumption; inv Heost.
        split; [|intros; exfalso; cbn in H1; solve_mesi].
        intros.
        eapply ObjsInvalid_impl; [apply ObjsInvalid_init|].
        simpl; intros.
        intro Hx; subst.
        eapply parent_not_in_subtree; eauto.
      + rewrite implOStatesInit_value_non_root in Heost by assumption; inv Heost.
        split; [|intros; exfalso; cbn in H2; solve_mesi].
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
        InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
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

  Lemma mesi_InvExcl_ext_in:
    forall oss orqs msgs,
      InvExcl topo cifc {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        InvExcl topo cifc {| bst_oss := oss;
                             bst_orqs := orqs;
                             bst_msgs := enqMsgs eins msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.
    dest; repeat ssplit.

    - clear H2 H3.
      red; intros.
      destruct H2.
      apply MsgsP_enqMsgs_inv in H3.
      specialize (H (conj H2 H3)); dest.

      split.
      + eapply ObjsInvalid_ext_in; eauto.
      + apply MsgsP_other_midx_enqMsgs; [assumption|].
        destruct H1; simpl.
        eapply DisjList_SubList; [eassumption|].
        eapply DisjList_comm, DisjList_SubList.
        * eapply SubList_trans;
            [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= eidx)].
          { solve_SubList. }
          { specialize (H0 eidx); simpl in H0.
            rewrite Heost in H0; simpl in H0.
            eassumption.
          }
        * apply tree2Topo_minds_merqs_disj.

    - clear H H3.
      red; intros.
      specialize (H2 H).
      eapply ObjsInvalid_ext_in; eauto.

    - clear H H2.
      red; intros.
      specialize (H3 H _ H2); dest.
      split; intros.
      + clear H4; specialize (H3 H5).
        eapply ObjsInvalid_ext_in; eauto.
      + clear H3; specialize (H4 H5).
        eapply ObjsInvalid_ext_in; eauto.
  Qed.

  Corollary mesi_InvExcl_InvTrsIns: InvTrsIns impl (InvExcl topo cifc).
  Proof.
    red; intros.
    inv H1.
    eapply mesi_InvExcl_ext_in; eauto.
    apply (mesi_InObjInds H).
  Qed.

  Lemma ObjsInvalid_ext_out:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall orqs,
        InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
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

  Lemma mesi_InvExcl_ext_out:
    forall oss orqs msgs,
      InvExcl topo cifc {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall (eouts: list (Id Msg)),
        ValidMsgsExtOut impl eouts ->
        InvExcl topo cifc {| bst_oss := oss;
                             bst_orqs := orqs;
                             bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.
    dest; repeat ssplit.

    - clear H2 H3.
      red; intros.
      destruct H2.
      apply MsgsP_other_midx_deqMsgs_inv in H3.
      + specialize (H (conj H2 H3)); dest.
        split.
        * eapply ObjsInvalid_ext_out; eauto.
        * apply MsgsP_deqMsgs; assumption.
      + destruct H1.
        simpl; eapply DisjList_SubList; [eassumption|].
        eapply DisjList_comm, DisjList_SubList.
        * eapply SubList_trans;
            [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= eidx)].
          { solve_SubList. }
          { specialize (H0 eidx); simpl in H0.
            rewrite Heost in H0; simpl in H0.
            eassumption.
          }
        * apply tree2Topo_minds_merss_disj.

    - clear H H3.
      red; intros.
      specialize (H2 H).
      eapply ObjsInvalid_ext_out; eauto.

    - clear H H2.
      red; intros.
      specialize (H3 H _ H2); dest.
      split; intros.
      + clear H4; specialize (H3 H5).
        eapply ObjsInvalid_ext_out; eauto.
      + clear H3; specialize (H4 H5).
        eapply ObjsInvalid_ext_out; eauto.
  Qed.

  Corollary mesi_InvExcl_InvTrsOuts: InvTrsOuts impl (InvExcl topo cifc).
  Proof.
    red; intros.
    inv H1.
    eapply mesi_InvExcl_ext_out; eauto.
    apply (mesi_InObjInds H).
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
    (valOf eout).(msg_id) = mesiRsM ->
    ObjsInvalid (fun idx => ~ In idx (subtreeIndsOf topo oidx)) oss msgs.

  Definition RsEPred (oidx: IdxT) (eout: Id Msg) (oss: OStates)
             (msgs: MessagePool Msg): Prop :=
    idOf eout = downTo oidx ->
    (valOf eout).(msg_type) = MRs ->
    (valOf eout).(msg_id) = mesiRsE ->
    ObjsInvalid (fun idx => oidx <> idx) oss msgs.

  Definition DownRsSPred (oidx: IdxT) (eout: Id Msg) (oss: OStates)
             (msgs: MessagePool Msg): Prop :=
    idOf eout = rsUpFrom oidx ->
    (valOf eout).(msg_type) = MRs ->
    (valOf eout).(msg_id) = mesiDownRsS ->
    ost <+- oss@[oidx]; (ost#[status] <= mesiS /\ ost#[owned] = false).
             
  Definition DownRsIPred (oidx: IdxT) (eout: Id Msg) (oss: OStates)
             (msgs: MessagePool Msg): Prop :=
    idOf eout = rsUpFrom oidx ->
    (valOf eout).(msg_type) = MRs ->
    (valOf eout).(msg_id) = mesiDownRsI ->
    ObjsInvalid (fun idx => In idx (subtreeIndsOf topo oidx)) oss msgs.

  Definition InvExclMsgOutPred: MsgOutPred :=
    fun eout oss orqs msgs =>
      forall oidx,
        GetRqPred oidx eout /\ SetRqPred oidx eout /\
        RsMPred oidx eout oss msgs /\ RsEPred oidx eout oss msgs /\
        DownRsSPred oidx eout oss msgs /\ DownRsIPred oidx eout oss msgs.

  Ltac disc_bind_true :=
    repeat
      match goal with
      | |- _ <+- ?ov; _ =>
        first [match goal with
               | [H: ov = _ |- _] => rewrite H in *; simpl in *
               end
              |let Hov := fresh "H" in
               let v := fresh "v" in
               destruct ov as [v|] eqn:Hov; simpl in *; [|auto]]
      end.

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
        try (red; intros; rewrite H9 in H1;
             derive_child_chns oidx; disc_rule_conds_ex; fail).

    - red; intros; destruct H.
      pose proof (rsEdgeUpFrom_Some (mesi_RqRsDTree Htr) _ H0).
      destruct H1 as [rqUp [down [pidx ?]]]; dest.
      do 2 (red; intros).
      specialize (H4 oidx0); dest.
      repeat ssplit;
        try (red; intros; rewrite H11 in H0;
             derive_child_chns oidx; disc_rule_conds_ex; fail).

      + (* [DownRsSPred] *)
        red; intros; rewrite H11 in H0.
        derive_child_chns oidx; disc_rule_conds_ex.
        assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) oidx))
          by (eapply rqEdgeUpFrom_subtreeIndsOf_self_in;
              [eauto|congruence]).
        pose proof (H5 _ H14); dest.
        rewrite <-H15; apply H9; assumption.

      + (* [DownRsIPred] *)
        red; intros; rewrite H11 in H0.
        derive_child_chns oidx; disc_rule_conds_ex.
        red; intros.
        specialize (H10 H11 H12 H13 _ H14).
        specialize (H5 _ H14); dest.
        rewrite <-H5.
        assert (exists pidx0, parentIdxOf (fst (tree2Topo tr 0)) oidx0 = Some pidx0).
        { eapply subtreeIndsOf_in_has_parent; eauto. }
        destruct H17 as [pidx0 ?].
        derive_child_chns oidx0.
        
        red in H16; dest.
        specialize (H16 _ H18).
        specialize (H21 _ H19).
        specialize (H22 _ H20).
        destruct (oss1@[oidx0]) as [ost0|]; simpl in *; auto.
        destruct H10; [left|right].
        * destruct H10; split; [assumption|].
          apply not_MsgExistsSig_MsgsNotExist; intros.
          eapply MsgExistsSig_MsgsNotExist_false in H23; eauto.
          dest_in.
          all: try (destruct H25 as [[midx msg] [? ?]];
                    exists (midx, msg); split; [|assumption]; inv H25;
                    do 2 red in H24; do 2 red; simpl in *; congruence).
        * destruct H10 as [[midx msg] [? ?]].
          exists (midx, msg); split; [|assumption]; inv H23.
          do 2 red in H10; do 2 red; simpl in *; congruence.
  Qed.
  Local Hint Resolve InvExclMsgOutPred_good.
  
  Ltac disc_rule_custom ::=
    try disc_AtomicInv.

  (*! Ltacs about [InvExcl] *)

  Ltac case_InvExcl_me_others :=
    match goal with
    | |- InvExcl _ _ _ => red; simpl; intros; mred; simpl
    end.

  Ltac case_InvObjOwned :=
    match goal with
    | [H: InvObjOwned _ _ _ _ _ |- InvObjOwned _ _ _ _ _] =>
      let Ho := fresh "H" in
      red; simpl; intros Ho; specialize (H Ho);
      red; intros; mred; simpl
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
      (* specialize (Hi oidx ltac:(auto)); disc_bind_true *)
      pose proof (Hi oidx ltac:(auto)); disc_bind_true
    end.

  Ltac disc_InvObjExcl0 :=
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
            simpl; solve_mesi)
    end.

  Ltac solve_InvObjExcl0_by_ObjExcl0_false :=
    red; intros; exfalso;
    match goal with
    | [H: ObjExcl0 _ _ _ |- _] =>
      red in H; dest; simpl in *; solve_mesi
    end.

  Local Hint Extern 0 (WfDTree topo) => apply tree2Topo_WfDTree.
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
      destruct H; split; [assumption|solve_MsgsP]
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
    simpl in *; solve [auto|solve_mesi].

  Ltac solve_by_ObjsInvalid_rsS_false roidx :=
    exfalso;
    eapply ObjsInvalid_rsS_false with (oidx:= roidx); eauto;
    apply FirstMP_InMP; assumption.
  
  Ltac solve_by_ObjsInvalid_rsE_false roidx :=
    exfalso;
    eapply ObjsInvalid_rsE_false with (oidx:= roidx); eauto;
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

  Ltac solve_InvObjOwned_by_false :=
    red; simpl; intros; discriminate.

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
                              [mesiRqS; mesiDownRqS;
                                 mesiRqM; mesiDownRqI; mesiDownRsI;
                                   mesiInvRq; mesiInvWRq;
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
                              [mesiRqS; mesiDownRqS;
                                 mesiRqM; mesiDownRqI; mesiDownRsI;
                                   mesiInvRq; mesiInvWRq; mesiInvRs;
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
      apply in_map_iff in H4; destruct H4 as [[rmidx msg] [? ?]].
      simpl in *; subst.
      rewrite Forall_forall in H0; specialize (H0 _ H5); simpl in H0.
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
      InvExcl topo cifc {| bst_oss := oss; bst_orqs := porqs; bst_msgs := msgs |} ->
      forall rmsgs,
        NoDup (idsOf rmsgs) ->
        Forall (FirstMPI msgs) rmsgs ->
        Forall (fun idm => In (msg_id (valOf idm))
                              [mesiRqS; mesiDownRqS;
                                 mesiRqM; mesiDownRqI; mesiDownRsI;
                                   mesiInvRq; mesiInvWRq;
                                     getRq; getRs; setRq; setRs]) rmsgs ->
        InvExcl topo cifc {| bst_oss := oss;
                             bst_orqs := norqs;
                             bst_msgs := deqMsgs (idsOf rmsgs) msgs |}.
  Proof.
    intros.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    disc_bind_true; dest; repeat ssplit.

    - red; intros.
      destruct H6.
      apply MsgsP_other_msg_id_deqMsgs_inv in H7; try assumption.
      + specialize (H (conj H6 H7)); dest; split.
        * apply ObjsInvalid_deq_sound; auto.
        * solve_MsgsP.
      + simpl.
        apply (DisjList_spec_1 idx_dec); intros midx ?.
        apply in_map_iff in H8; destruct H8 as [[rmidx msg] [? ?]].
        simpl in *; subst.
        rewrite Forall_forall in H2; specialize (H2 _ H9); simpl in H2.
        intro Hx; destruct Hx; [|auto].
        rewrite <-H8 in H2.
        intuition discriminate.
    - red; intros.
      specialize (H4 H6).
      apply ObjsInvalid_deq_sound; auto.
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
      InvExcl topo cifc {| bst_oss := oss; bst_orqs := porqs; bst_msgs := msgs |} ->
      forall nmsgs,
        Forall (fun idm => In (msg_id (valOf idm))
                              [mesiRqS; mesiDownRqS;
                                 mesiRqM; mesiDownRqI; mesiDownRsI;
                                   mesiInvRq; mesiInvWRq; mesiInvRs;
                                     getRq; getRs; setRq; setRs]) nmsgs ->
        InvExcl topo cifc {| bst_oss := oss;
                             bst_orqs := norqs;
                             bst_msgs := enqMsgs nmsgs msgs |}.
  Proof.
    intros.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    disc_bind_true; dest; repeat ssplit.

    - disc_InvObjExcl0; split.
      + apply ObjsInvalid_enq_sound; auto.
      + apply MsgsP_other_msg_id_enqMsgs; [assumption|].
        simpl.
        apply (DisjList_spec_1 idx_dec); intros midx ?.
        apply in_map_iff in H6; destruct H6 as [[rmidx msg] [? ?]].
        simpl in *; subst.
        rewrite Forall_forall in H0; specialize (H0 _ H7); simpl in H0.
        intro Hx.
        repeat
          match goal with
          | [H: _ \/ _ |- _] => destruct H
          | [H1: _ = msg_id ?msg, H2: _ = msg_id ?msg |- _] =>
            rewrite <-H1 in H2; discriminate
          | [H: False |- False] => auto
          end.
    - red; intros.
      specialize (H2 H4).
      apply ObjsInvalid_enq_sound; auto.
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
        (nost#[status] <= mesiI \/ nost#[status] <= post#[status]) ->
        ObjsInvalid inP (oss +[oidx <- nost]) msgs.
  Proof.
    intros.
    red; intros.
    specialize (H _ H2).
    mred; simpl; auto.
    destruct H; [left|right].
    - destruct H; split; [solve_mesi|assumption].
    - assumption.
  Qed.

  Lemma InvDirInv_state_transition_sound:
    forall eidx eost oss msgs,
      InvDirInv topo cifc eidx eost oss msgs ->
      forall oidx (post nost: OState),
        oss@[oidx] = Some post ->
        (nost#[status] <= mesiI \/ nost#[status] <= post#[status]) ->
        nost#[dir] = post#[dir] ->
        InvDirInv topo cifc eidx eost (oss +[oidx <- nost]) msgs.
  Proof.
    intros.
    red; intros; specialize (H H3 _ H4).
    dest; split.
    - intros; specialize (H H6).
      eapply ObjsInvalid_state_transition_sound; eauto.
    - intros; specialize (H5 H6).
      eapply ObjsInvalid_state_transition_sound; eauto.
  Qed.    

  Lemma InvExcl_state_transition_sound:
    forall oss porqs msgs,
      InvExcl topo cifc {| bst_oss := oss; bst_orqs := porqs; bst_msgs := msgs |} ->
      forall oidx (post nost: OState) norqs,
        oss@[oidx] = Some post ->
        (nost#[status] <= mesiI \/ nost#[status] <= post#[status]) ->
        post#[owned] || negb (nost#[owned]) = true ->
        nost#[dir] = post#[dir] ->
        InvExcl topo cifc {| bst_oss := oss +[oidx <- nost];
                             bst_orqs := norqs; bst_msgs := msgs |}.
  Proof.
    intros.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    mred; simpl; dest.
    - repeat ssplit.
      + red; intros.
        destruct H6.
        assert (mesiE <= post#[status]) by solve_mesi.
        specialize (H (conj H8 H7)); dest.
        split; [|assumption].
        eapply ObjsInvalid_state_transition_sound; eauto.
      + red; intros.
        rewrite H6 in H2; simpl in H2.
        rewrite orb_false_r in H2.
        specialize (H4 H2).
        eapply ObjsInvalid_state_transition_sound; eauto.
      + red; intros.
        specialize (H5 H6 _ H7); dest.
        split; intros.
        * rewrite <-H3 in H5; specialize (H5 H9).
          eapply ObjsInvalid_state_transition_sound; eauto.
        * rewrite <-H3 in H8; specialize (H8 H9).
          eapply ObjsInvalid_state_transition_sound; eauto.
          
    - disc_bind_true; dest; repeat ssplit.
      + red; intros; specialize (H H7); dest.
        split; [|assumption].
        eapply ObjsInvalid_state_transition_sound; eauto.
      + red; intros.
        specialize (H5 H7).
        eapply ObjsInvalid_state_transition_sound; eauto.
      + red; intros.
        specialize (H6 H7 _ H8); dest.
        split; intros.
        * specialize (H6 H10).
          eapply ObjsInvalid_state_transition_sound; eauto.
        * specialize (H9 H10).
          eapply ObjsInvalid_state_transition_sound; eauto.
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
        | |- InvExcl _ _ {| bst_oss := ?oss +[?oidx <- ?pos] |} =>
          replace (oss +[oidx <- pos]) with oss by meq
        end;
    repeat
      match goal with
      | [He: InvExcl _ _ {| bst_orqs := ?orqs |}
         |- InvExcl _ _ {| bst_msgs := enqMP ?midx ?msg _ |}] =>
        eapply InvExcl_enq_sound with (porqs:= orqs) (nmsgs:= [(midx, msg)]);
        [|solve_InvExcl_msgs; fail]
      | [He: InvExcl _ _ {| bst_orqs := ?orqs |},
             Hf: FirstMPI _ (?midx, ?msg)
         |- InvExcl _ _ {| bst_msgs := deqMP ?midx _ |}] =>
        eapply InvExcl_deq_sound with (porqs:= orqs) (rmsgs:= [(midx, msg)]);
        [|solve_InvExcl_msgs; fail..]
      | [He: InvExcl _ _ {| bst_orqs := ?orqs |}
         |- InvExcl _ _ {| bst_msgs := enqMsgs _ _ |}] =>
        eapply InvExcl_enq_sound with (porqs:= orqs); [|solve_InvExcl_msgs; fail]
      | [He: InvExcl _ _ {| bst_orqs := ?orqs |}
         |- InvExcl _ _ {| bst_msgs := deqMsgs _ _ |}] =>
        eapply InvExcl_deq_sound with (porqs:= orqs); [|solve_InvExcl_msgs; fail..]
      end; try eassumption.

  Ltac admit_msg_pred := admit.

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
    | [Hrr: RqRsDownMatch _ _ _ ?rss _, Hrss: [_] = ?rss |- _] =>
      rewrite <-Hrss in Hrr;
      let Hrr0 := fresh "H" in
      pose proof Hrr as Hrr0;
      eapply RqRsDownMatch_rs_rq in Hrr0; [|left; reflexivity];
      let cidx := fresh "cidx" in 
      let down := fresh "down" in
      destruct Hrr0 as [cidx [down ?]]; dest
    end.

  Ltac pick_rsUps_one :=
    repeat
      match goal with
      | [Hrr: RqRsDownMatch _ _ _ ?rss _, Hrss: _ = ?rss |- _] =>
        rewrite <-Hrss in Hrr
      end;
    repeat
      match goal with
      | [Hrr: RqRsDownMatch _ _ _ (idsOf ?ins) _ |- _] =>
        pose proof (RqRsDownMatch_rs_not_nil Hrr);
        let midx := fresh "midx" in
        let msg := fresh "msg" in
        destruct ins as [|[midx msg] ins]; [exfalso; auto|];
        simpl in Hrr; eapply RqRsDownMatch_rs_rq in Hrr; [|left; reflexivity];
        let cidx := fresh "cidx" in
        let down := fresh "down" in
        destruct Hrr as [cidx [down ?]]; dest
      | [H: SubList (idsOf (_ :: _)) _ |- _] =>
        simpl in H; apply SubList_cons_inv in H; dest
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
           ]).

  Ltac disc_InvObjOwned :=
    match goal with
    | [H: InvObjOwned _ _ _ _ _ |- InvObjOwned _ _ _ _ _] =>
      let Ho := fresh "H" in
      red; simpl; intros Ho; try specialize (H Ho)
    end.

  Ltac solve_AtomicInv_init :=
    do 2 red; simpl;
    repeat constructor;
    try (red; simpl; intros; intuition discriminate).

  Lemma mesi_InvExcl_InvTrs_init:
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
  Proof. (* SKIP_PROOF_OFF *)
    intros.

    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (mesi_InObjInds H) as Hioi.
    pose proof (mesi_MsgConflictsInv
                  (@mesi_RootChnInv_ok _ Htr) H) as Hpmcf.
    pose proof (@MesiUpLockInv_ok _ Htr _ H) as Hulinv.
    pose proof (@MesiDownLockInv_ok _ Htr _ H) as Hdlinv.

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
      apply in_app_or in H8; destruct H8.

      1: { (** Rules per a child *)
        apply concat_In in H3; destruct H3 as [crls [? ?]].
        apply in_map_iff in H3; destruct H3 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in; disc_rule_conds_ex.
        all: try (exfalso_InvTrs_init; fail).
      }

      dest_in.

      { disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx;
          [|derive_child_chns x; solve_midx_false].
        disc_responses_from.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }
      { disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx;
          [|derive_child_chns x; solve_midx_false].
        pick_rsUps_one.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }

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

      { disc_MesiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx.
        disc_responses_from.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }
      { disc_MesiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx; [solve_midx_false|].
        disc_responses_from.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }

      { disc_MesiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx.
        pick_rsUps_one.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }
      { disc_MesiDownLockInv oidx Hdlinv.
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
          { simpl; intuition solve_mesi. }
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
      
      { (* [l1GetSRsDownDownE] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        exfalso_InvTrs_init.
      }

      { (* [l1DownSImm] *)
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }

      { (* [l1GetMImmE] *)
        disc_rule_conds_ex.
        derive_NoRsI_by_no_uplock oidx msgs.

        split.
        { solve_AtomicInv_init. }
        { solve_InvExcl_trivial.
          case_InvExcl_me_others.
          { assert (ObjExcl0 oidx os msgs)
              by (split; [simpl in *; solve_mesi|assumption]).
            disc_InvExcl_this.
            { specialize (H0 H9); dest.
              red; intros.
              split; [|assumption].
              red; intros; specialize (H0 _ H25); mred.
            }
            { specialize (H0 H9); dest.
              red; intros _.
              red; intros.
              mred; [solve_by_topo_false|auto].
            }
            { red; intros; exfalso.
              pose proof (tree2Topo_WfCIfc tr 0) as [? _].
              apply (DisjList_NoDup idx_dec) in H25.
              eapply DisjList_In_1; eassumption.
            }
          }
          { disc_InvExcl_others.
            { disc_InvObjExcl0.
              solve_by_ObjsInvalid_status_false oidx.
            }
            { case_InvObjOwned.
              { solve_by_ObjsInvalid_status_false oidx. }
              { auto. }
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

      { (* [l1GetMImmM] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_init. }
        { eapply InvExcl_state_transition_sound with (porqs:= orqs);
            try eassumption.
          { solve_InvExcl_trivial. }
          { simpl; auto. }
          { simpl; intuition. }
          { reflexivity. }
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

      { (* [l1DownIImm] *)
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }

      { (* [l1InvRqUpUp] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_init. }
        { solve_InvExcl_trivial. }
      }
      
      { (* [l1InvRqUpUpWB] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_init. }
        { solve_InvExcl_trivial. }
      }
      
      { (* [l1InvRsDownDown] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        exfalso_InvTrs_init.
      }

      Unshelve.
      all: assumption.

      (* END_SKIP_PROOF_OFF *)
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
               Hi: msg_id ?rmsg = mesiRsM |- _] =>
      specialize (Hp eq_refl Ht Hi)
    | [Hp: RsEPred _ (_, ?rmsg) _ _,
           Ht: msg_type ?rmsg = _,
               Hi: msg_id ?rmsg = mesiRsE |- _] =>
      specialize (Hp eq_refl Ht Hi)
    | [Hp: DownRsSPred _ (_, ?rmsg) _ _,
           Ht: msg_type ?rmsg = _,
               Hi: msg_id ?rmsg = mesiDownRsS |- _] =>
      specialize (Hp eq_refl Ht Hi)
    | [Hp: DownRsIPred _ (_, ?rmsg) _ _,
           Ht: msg_type ?rmsg = _,
               Hi: msg_id ?rmsg = mesiDownRsI |- _] =>
      specialize (Hp eq_refl Ht Hi)
    end.

  Ltac solve_AtomicInv_rqDown_rqDowns :=
    match goal with
    | [Hr: Reachable _ _ ?st,
           Hs: steps _ _ ?st ?hst _,
               Ha: Atomic _ _ _ ?hst _ ?eouts,
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
    end.

  Ltac solve_AtomicInv_rsDown :=
    match goal with
    | [Hr: Reachable _ _ ?st,
           Hs: steps _ _ ?st ?hst _,
               Ha: Atomic _ _ _ ?hst _ ?eouts,
                   Hin: In (downTo ?roidx, _) ?eouts
       |- AtomicInv _ _ _ _ _ _] =>
      do 2 red; simpl;
      eapply atomic_rsDown_singleton with (oidx:= roidx) in Ha;
      try exact Hr; eauto; [|red; auto];
      subst; rewrite removeOnce_nil; simpl;
      repeat constructor; try (red; simpl; intros; intuition discriminate)
    end.

  Ltac solve_AtomicInv_rqDown_rsUp :=
    match goal with
    | [Hr: Reachable _ _ ?st,
           Hs: steps _ _ ?st ?hst _,
               Ha: Atomic _ _ _ ?hst _ ?eouts,
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

  Ltac solve_msg_pred_base :=
    let Hm := fresh "H" in
    red; simpl; intros Hm _ _; inv Hm; mred.

  Ltac solve_DownRsSPred :=
    solve_msg_pred_base; mred.

  Ltac disc_dir :=
    repeat
      match goal with
      | [H: context[getDir _ _] |- _] => progress simpl in H
      | [H: context[getDir _ (addSharer _ _)] |- _] =>
        rewrite getDir_addSharer_spec in H by solve_mesi;
        destruct (idx_dec _ _) in H; try solve_mesi

      | [H: context[getDir ?cidx (setDirE ?cidx)] |- _] =>
        rewrite getDir_setDirE_eq in H
      | [Hn: ?oidx1 <> ?oidx2, H: context[getDir ?oidx1 (setDirE ?oidx2)] |- _] =>
        rewrite getDir_setDirE_neq in H by auto
      | [Hn: ?oidx2 <> ?oidx1, H: context[getDir ?oidx1 (setDirE ?oidx2)] |- _] =>
        rewrite getDir_setDirE_neq in H by auto

      | [H: context[getDir ?cidx (setDirM ?cidx)] |- _] =>
        rewrite getDir_setDirM_eq in H
      | [Hn: ?oidx1 <> ?oidx2, H: context[getDir ?oidx1 (setDirM ?oidx2)] |- _] =>
        rewrite getDir_setDirM_neq in H by auto
      | [Hn: ?oidx2 <> ?oidx1, H: context[getDir ?oidx1 (setDirM ?oidx2)] |- _] =>
        rewrite getDir_setDirM_neq in H by auto
      end;
    try match goal with
        | [H: mesiS <= getDir ?cidx ?dir |- _] =>
          pose proof (getDir_st_sound dir cidx ltac:(solve_mesi))
        | [H: mesiE <= getDir ?cidx ?dir |- _] =>
          pose proof (getDir_st_sound dir cidx ltac:(solve_mesi))
        end.

  Lemma mesi_InvExcl_InvTrs: InvTrs impl (InvExcl topo cifc).
  Proof.
    eapply inv_atomic_InvTrs;
      [red; intros; eapply mesi_InvExcl_InvTrsIns; eauto
      |red; intros; eapply mesi_InvExcl_InvTrsOuts; eauto
      |].
    instantiate (1:= AtomicInv InvExclMsgOutPred).

    red; intros.
    destruct H1.
    generalize dependent ist2.

    induction H3; simpl; intros; subst;
      [inv_steps; apply mesi_InvExcl_InvTrs_init; auto|].

    assert (Atomic msg_dec inits (ins ++ rins) (RlblInt oidx ridx rins routs :: hst)
                   (outs ++ routs) (removeL (id_dec msg_dec) eouts rins ++ routs)) as Hnatm
        by (econstructor; eauto).
    pose proof (atomic_rsDown_singleton
                  (mesi_GoodORqsInit Htr)
                  (mesi_RqRsSys Htr)
                  Hnatm H H8) as Hrsd.
    clear Hnatm.

    inv_steps.
    pose proof (reachable_steps H H9) as Hr1.
    pose proof (reachable_steps Hr1 (steps_singleton H11)) as Hr2.

    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) Hr1) as Hftinv.
    pose proof (mesi_InObjInds Hr1) as Hioi1.
    pose proof (mesi_InObjInds Hr2) as Hioi2.
    pose proof (mesi_OstInds Hr1) as Hosi.
    pose proof (mesi_MsgConflictsInv
                  (@mesi_RootChnInv_ok _ Htr) Hr1) as Hpmcf.
    pose proof (@MesiUpLockInv_ok _ Htr _ Hr1) as Hulinv.
    pose proof (@MesiDownLockInv_ok _ Htr _ Hr1) as Hdlinv.

    specialize (IHAtomic H1 _ H9); dest.
    inv_step.

    simpl in H13; destruct H13; [subst|apply in_app_or in H7; destruct H7].
    
    - (*! Cases for the main memory *)

      (** Abstract the root. *)
      assert (In (rootOf (fst (tree2Topo tr 0)))
                 (c_li_indices (snd (tree2Topo tr 0)))) as Hin.
      { rewrite c_li_indices_head_rootOf by assumption.
        left; reflexivity.
      }

      remember (rootOf (fst (tree2Topo tr 0))) as oidx; clear Heqoidx.

      (** Do case analysis per a rule. *)
      apply in_app_or in H14; destruct H14.

      1: { (** Rules per a child *)
        apply concat_In in H7; destruct H7 as [crls [? ?]].
        apply in_map_iff in H7; destruct H7 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        (*
        
        dest_in.

        { (* [liGetSImmS] *)
          disc_rule_conds_ex.
          derive_NoRsI_by_no_uplock oidx msgs.
          
          split.
          { admit_msg_pred. }
          { case_InvExcl_me_others.
            { disc_InvExcl_this; [solve_InvObjExcl0_by_ObjExcl0_false|].
              case_InvObjOwned; [solve_by_topo_false|].
              disc_ObjsInvalid_by oidx0.
              case_ObjInvalid_with cidx; [solve_by_topo_false|].
              case_ObjInvalid; [solve_ObjInvalid0|].
              solve_ObjInvRs.
            }

            { disc_InvExcl_others.
              { disc_InvObjExcl0.
                solve_by_ObjsInvalid_status_false oidx.
              }
              { case_InvObjOwned; [solve_by_ObjsInvalid_status_false oidx|].
                derive_not_InvalidObj_not_in oidx.
                disc_ObjsInvalid_by oidx0.
                case_ObjInvalid_with cidx; [solve_by_topo_false|].
                case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
              }
            }
          }
        }

        { (* [liGetSImmME] *)
          disc_rule_conds_ex.
          derive_NoRsI_by_no_uplock oidx msgs.

          split.
          { admit_msg_pred. }
          { case_InvExcl_me_others.
            { disc_InvExcl_this; [solve_InvObjExcl0_by_ObjExcl0_false|].
              case_InvObjOwned; [solve_by_topo_false|].
              disc_ObjsInvalid_by oidx0.
              case_ObjInvalid_with cidx; [solve_by_topo_false|].
              case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
            }

            { disc_InvExcl_others.
              { disc_InvObjExcl0.
                solve_by_ObjsInvalid_status_false oidx.
              }
              { case_InvObjOwned; [solve_by_ObjsInvalid_status_false oidx|].
                derive_not_InvalidObj_not_in oidx.
                disc_ObjsInvalid_by oidx0.
                case_ObjInvalid_with cidx; [solve_by_topo_false|].
                case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
              }
            }
          }
        }

        { (* [liGetSRqUpDownME] *)
          disc_rule_conds_ex; split.
          { admit_msg_pred. }
          { solve_InvExcl_trivial. }
        }

        { (* [liGetMImm] *) admit. }

        { (* [liGetMRqUpDownME] *)
          disc_rule_conds_ex; split.
          { admit_msg_pred. }
          { solve_InvExcl_trivial. }
        }
        { (* [liGetMRqUpDownS] *)
          disc_rule_conds_ex; split.
          { admit_msg_pred. }
          { solve_InvExcl_trivial. }
        }

        { (* [liInvImmI] *) admit. }
        { (* [liInvImmS0] *) admit. }
        { (* [liInvImmS1] *) admit. }
        { (* [liInvImmE] *) admit. }
        { (* [liInvImmWBI] *) admit. }
        { (* [liInvImmWBS1] *) admit. }
        { (* [liInvImmWBME] *) admit. }

        *) admit.
      }

      dest_in.
      all: admit.

    - (*! Cases for Li caches *)
      pose proof H7 as Hobj.
      apply in_map_iff in H7; destruct H7 as [oidx [? ?]]; subst; simpl in *.

      pose proof (c_li_indices_tail_has_parent Htr _ _ H8).
      destruct H7 as [pidx [? ?]].
      pose proof (Htn _ _ H10); dest.

      (** Do case analysis per a rule. *)
      apply in_app_or in H14; destruct H14.

      1: { (** Rules per a child *)
        apply concat_In in H14; destruct H14 as [crls [? ?]].
        apply in_map_iff in H14; destruct H14 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        (*

        dest_in.
        
        { (* [liGetSImmS] *)
          disc_rule_conds_ex.
          derive_NoRsI_by_no_uplock oidx msgs.
          
          split.
          { admit_msg_pred. }
          { case_InvExcl_me_others.
            { disc_InvExcl_this; [solve_InvObjExcl0_by_ObjExcl0_false|].
              case_InvObjOwned; [solve_by_topo_false|].
              disc_ObjsInvalid_by oidx0.
              case_ObjInvalid_with cidx; [solve_by_topo_false|].
              case_ObjInvalid; [solve_ObjInvalid0|].
              solve_ObjInvRs.
            }

            { disc_InvExcl_others.
              { disc_InvObjExcl0.
                solve_by_ObjsInvalid_status_false oidx.
              }
              { case_InvObjOwned; [solve_by_ObjsInvalid_status_false oidx|].
                derive_not_InvalidObj_not_in oidx.
                disc_ObjsInvalid_by oidx0.
                case_ObjInvalid_with cidx; [solve_by_topo_false|].
                case_ObjInvalid; [solve_ObjInvalid0|].
                solve_ObjInvRs.
              }
            }
          }
        }

        { (* [liGetSImmME] *)
          disc_rule_conds_ex.
          derive_NoRsI_by_no_uplock oidx msgs.
          
          split.
          { admit_msg_pred. }
          { case_InvExcl_me_others.
            { disc_InvExcl_this; [solve_InvObjExcl0_by_ObjExcl0_false|].
              case_InvObjOwned; [solve_by_topo_false|].
              disc_ObjsInvalid_by oidx0.
              case_ObjInvalid_with cidx; [solve_by_topo_false|].
              case_ObjInvalid; [solve_ObjInvalid0|].
              solve_ObjInvRs.
            }

            { disc_InvExcl_others.
              { disc_InvObjExcl0.
                solve_by_ObjsInvalid_status_false oidx.
              }
              { case_InvObjOwned; [solve_by_ObjsInvalid_status_false oidx|].
                derive_not_InvalidObj_not_in oidx.
                disc_ObjsInvalid_by oidx0.
                case_ObjInvalid_with cidx; [solve_by_topo_false|].
                case_ObjInvalid; [solve_ObjInvalid0|].
                solve_ObjInvRs.
              }
            }
          }
        }
          
        { (* [liGetSRqUpUp] *)
          disc_rule_conds_ex; split.
          { admit_msg_pred. }
          { solve_InvExcl_trivial. }
        }

        { (* [liGetSRqUpDownME] *)
          disc_rule_conds_ex; split.
          { admit_msg_pred. }
          { solve_InvExcl_trivial. }
        }

        { (* [liGetMImm] *)
          disc_rule_conds_ex.
          derive_NoRsI_by_no_uplock oidx msgs.
          
          split.
          { admit_msg_pred. }
          { case_InvExcl_me_others.
            { disc_InvExcl_this; [solve_InvObjExcl0_by_ObjExcl0_false|].
              case_InvObjOwned; [solve_by_topo_false|].
              disc_ObjsInvalid_by oidx0.
              case_ObjInvalid_with cidx; [solve_by_topo_false|].
              case_ObjInvalid; [solve_ObjInvalid0|].
              solve_ObjInvRs.
            }

            { disc_InvExcl_others.
              { disc_InvObjExcl0.
                solve_by_ObjsInvalid_status_false oidx.
              }
              { case_InvObjOwned; [solve_by_ObjsInvalid_status_false oidx|].
                derive_not_InvalidObj_not_in oidx.
                disc_ObjsInvalid_by oidx0.
                case_ObjInvalid_with cidx; [solve_by_topo_false|].
                case_ObjInvalid; [solve_ObjInvalid0|].
                solve_ObjInvRs.
              }
            }
          }
        }

        { (* [liGetMRqUpUp] *)
          disc_rule_conds_ex; split.
          { admit_msg_pred. }
          { solve_InvExcl_trivial. }
        }

        { (* [liGetMRqUpDownME] *)
          disc_rule_conds_ex; split.
          { admit_msg_pred. }
          { solve_InvExcl_trivial. }
        }

        { (* [liGetMRqUpDownS] *)
          disc_rule_conds_ex; split.
          { admit_msg_pred. }
          { solve_InvExcl_trivial. }
        }

        { (* [liInvImmI] *)
          disc_rule_conds_ex; split.
          { admit_msg_pred. }
          { solve_InvExcl_trivial. }
        }

        { (* [liInvImmS0] *)
          disc_rule_conds_ex; split.
          { admit_msg_pred. }
          { solve_InvExcl_trivial.
            eapply InvExcl_state_transition_sound; try eassumption.
            { simpl; auto. }
            { simpl; intuition. }
          }
        }
          
        { (* [liInvImmS1] *)
          disc_rule_conds_ex; split.
          { admit_msg_pred. }
          { solve_InvExcl_trivial.
            eapply InvExcl_state_transition_sound; try eassumption.
            { simpl; auto. }
            { simpl; intuition. }
          }
        }

        { (* [liInvImmE] *)
          (** TODO: need to draw (maybe from Dir-Invalid invariant?)
           * If dirE(C) then ObjsInvalid(~ tr(C)). *)
          admit.
        }

        { (* [liInvImmWBI] *)
          disc_rule_conds_ex; split.
          { admit_msg_pred. }
          { solve_InvExcl_trivial. }
        }

        { (* [liInvImmWBS1] *)
          disc_rule_conds_ex; split.
          { admit_msg_pred. }
          { solve_InvExcl_trivial.
            eapply InvExcl_state_transition_sound; try eassumption.
            { simpl; auto. }
            { simpl; intuition. }
          }
        }

        { (* [liInvImmWBME] *)
          (** TODO: need to draw (maybe from Dir-Invalid invariant?)
           * If dirM(C) then ObjsInvalid(~ tr(C)). *)
          admit.
        }

        *) admit.
        
      }

      dest_in.

      { (* [liGetSRsDownDownS] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        disc_MesiUpLockInv oidx.
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
                specialize (H37 H41).
                solve_ObjsInvalid_trivial.
              }
              { exfalso; disc_dir; solve_mesi. }
            }
          }

          { disc_MsgConflictsInv oidx.
            disc_InvExcl_others.
            { disc_InvObjExcl0.
              solve_by_ObjsInvalid_rsS_false oidx.
            }
            { case_InvObjOwned; [solve_by_ObjsInvalid_rsS_false oidx|].
              disc_ObjsInvalid_by oidx0; case_ObjInvalid.
              { case_idx_eq oidx0 cidx; [|solve_ObjInvalid0].
                eapply outside_parent_out in H46; eauto.
                solve_by_ObjsInvalid_rsS_false oidx.
              }
              { solve_ObjInvRs. }
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

      { (* [liGetSRsDownDownE] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_MsgConflictsInv oidx.
        disc_rule_conds_ex.

        split.
        { solve_AtomicInv_rsDown.
          disc_AtomicMsgOutsInv oidx.
          disc_MsgPred.

          solve_msg_pred_base.
          solve_ObjsInvalid_trivial.
          eapply ObjsInvalid_rsE; eauto.
        }
        { solve_InvExcl_trivial.
          case_InvExcl_me_others.
          { disc_InvExcl_this.
            { solve_InvObjExcl0_by_ObjExcl0_false. }
            { solve_InvObjOwned_by_false. }
            { split_InvDirInv.
              { case_idx_eq cidx cidx0; [disc_dir; discriminate|].
                disc_AtomicMsgOutsInv oidx.
                disc_MsgPred.
                solve_ObjsInvalid_trivial.
                eapply ObjsInvalid_impl; [eassumption|].
                simpl; intros.
                intro; subst; solve_by_topo_false.
              }
              { case_idx_eq cidx cidx0; [|disc_dir; solve_mesi].
                disc_AtomicMsgOutsInv oidx.
                disc_MsgPred.
                solve_ObjsInvalid_trivial.
                eapply ObjsInvalid_impl.
                { eapply ObjsInvalid_rsE; eauto. }
                { simpl; intros.
                  intro; subst; solve_by_topo_false.
                }
              }
            }
          }

          { disc_InvExcl_others.
            { disc_InvObjExcl0.
              solve_by_ObjsInvalid_rsE_false oidx.
            }
            { case_InvObjOwned; [solve_by_ObjsInvalid_rsE_false oidx|].
              disc_ObjsInvalid_by oidx0; case_ObjInvalid.
              { case_idx_eq oidx0 cidx; [|solve_ObjInvalid0].
                eapply outside_parent_out in H43; eauto.
                solve_by_ObjsInvalid_rsE_false oidx.
              }
              { solve_ObjInvRs. }
            }
            { split_InvDirInv_apply.
              { case_in_subtree oidx cidx0.
                { solve_by_ObjsInvalid_rsE_false oidx. }
                { solve_ObjsInvalid_trivial. }
              }
              { case_in_subtree oidx cidx0.
                { solve_ObjsInvalid_trivial. }
                { solve_by_ObjsInvalid_rsE_false oidx. }
              }
            }
          }
        }
      }

      { (* [liDownSRsUpDownME] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx.

        split.
        { solve_AtomicInv_rsUps_rsDown Hrsd. }
        { apply subtreeChildrenIndsOf_parentIdxOf in H30; auto.
          case_InvExcl_me_others.
          { disc_InvExcl_this.
            { solve_InvObjExcl0_by_ObjExcl0_false. }
            { disc_InvObjOwned.

              (** TODO Ltac [disc_InvDirInv cidx] *)
              move H40 at bottom.
              red in H40.
              specialize (H40 (tl_In _ _ H8)).
              specialize (H40 _ H30); dest.

              rewrite getDir_excl_eq in H42; [|reflexivity|intuition solve_mesi].
              specialize (H42 H24).

              remember (dir_excl _) as rcidx; clear Heqrcidx.

              solve_ObjsInvalid_trivial.
              eapply ObjsInvalid_impl; [eassumption|].
              simpl; intros.
              intro Hx; elim H43.
              eapply subtreeIndsOf_child_SubList with (cidx:= rcidx); eauto.
            }
            { remember (dir_excl _) as rcidx.
              split_InvDirInv.
              { apply getDir_setDirS_I_imp in H44.
                case_idx_eq x cidx; [exfalso; elim H44; left; reflexivity|].
                case_idx_eq rcidx cidx; [exfalso; elim H44; right; left; reflexivity|].
                solve_ObjsInvalid_trivial.
                apply H40.
                eapply getDir_excl_neq; [reflexivity|intuition solve_mesi|simpl; congruence].
              }
              { exfalso.
                pose proof (getDir_setDirS_sound cidx [x; rcidx]).
                simpl in *; solve_mesi.
              }
            }
          }

          { pose proof Hpmcf as Hpmcf'; phide Hpmcf'; rename H40 into Hpmcf'.
            disc_MsgConflictsInv oidx.
            remember (dir_excl _) as rcidx; clear Heqrcidx.
            disc_AtomicMsgOutsInv rcidx.

            (** TODO: Ltac [derive_child_st rcidx] *)
            pose proof (tree2Topo_li_child_li_l1 _ _ _ (tl_In _ _ H8) H30).
            pose proof (Hosi _ H51); simpl in H52.
            destruct H52 as [[rcost ?] [rcorq ?]].
            disc_MsgPred.
            rewrite H52 in H49; simpl in H49; dest.
            preveal Hpmcf'; disc_MsgConflictsInv rcidx.

            disc_InvExcl_others.
            { disc_InvObjExcl0.
              exfalso.
              case_idx_eq eidx rcidx.
              { disc_rule_conds; disc_ObjExcl0; solve_mesi. }
              { solve_by_ObjsInvalid_downRsS_false rcidx. }
            }
            { case_in_subtree rcidx eidx;
                [|disc_InvObjOwned; solve_by_ObjsInvalid_downRsS_false rcidx].
              case_idx_eq eidx rcidx;
                [disc_rule_conds; disc_InvObjOwned; congruence|].
              disc_InvObjOwned.
              (* Too complicated to put in [solve_by_topo_false]? *)
              assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) eidx)).
              { eapply inside_parent_in with (cidx:= rcidx); eauto. }
              solve_ObjsInvalid_trivial.
            }
            { split_InvDirInv_apply.
              { case_in_subtree x cidx.
                { case_idx_eq x cidx; [disc_rule_conds|].
                  (* Too complicated to put in [solve_by_topo_false]? *)
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
                (* Too complicated to put in [solve_by_topo_false]? *)
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
          simpl; intuition solve_mesi.
        }
        { case_InvExcl_me_others.
          { disc_InvExcl_this.
            { solve_InvObjExcl0_by_ObjExcl0_false. }
            { solve_InvObjOwned_by_false. }
            { split_InvDirInv_apply.
              { solve_ObjsInvalid_trivial. }
              { exfalso; disc_dir; solve_mesi. }
            }
          }
          { disc_InvExcl_others.
            { disc_InvObjExcl0.
              solve_by_ObjsInvalid_status_false oidx.
            }
            { case_InvObjOwned; [solve_by_ObjsInvalid_status_false oidx|].
              disc_ObjsInvalid_by oidx0.
              case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
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

      { (* [liDownSRqDownDownME] *)
        disc_rule_conds_ex; split.
        { remember (dir_excl _) as cidx; clear Heqcidx.
          solve_AtomicInv_rqDown_rqDowns.
          apply subtreeChildrenIndsOf_parentIdxOf in H24; auto.
          derive_child_chns cidx.
          repeat constructor; simpl; eauto.
        }
        { solve_InvExcl_trivial. }
      }

      { (* [liDownSRsUpUp] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx; [solve_midx_false|].

        pick_rsUp_single.

        split.
        { (** TODO: Ltac [solve_AtomicInv_rsUps_rsUp] *)
          match goal with
          | [Hr: Reachable _ _ ?st,
                 Hs: steps _ _ ?st ?hst _,
                     Ha: Atomic _ _ _ ?hst _ ?eouts,
                         H: FirstMPI _ (?midx, ?msg) |- context [deqMP ?midx _] ] =>
            do 2 red; simpl;
              apply Forall_app;
              [change midx with (idOf (midx, msg)) at 1;
               eapply atomic_rsUps_rsUp_preserves_msg_out_preds
                 with (rsUps:= [(midx, msg)]);
               try exact Hr; eauto
              |repeat constructor;
               try (red; simpl; intros; intuition discriminate)]
          end.
          { instantiate (1:= li tr oidx).
            right; apply in_or_app; left; auto.
          }
          { reflexivity. }
          { solve_NoDup. }
          { apply SubList_cons; [assumption|apply SubList_nil]. }

          solve_DownRsSPred.
          simpl; intuition solve_mesi.
        }
        { apply subtreeChildrenIndsOf_parentIdxOf in H30; auto.
          case_InvExcl_me_others.
          { disc_InvExcl_this.
            { solve_InvObjExcl0_by_ObjExcl0_false. }
            { solve_InvObjOwned_by_false. }
            { remember (dir_excl _) as rcidx.
              split_InvDirInv.
              { apply getDir_setDirS_I_imp in H44.
                case_idx_eq rcidx cidx0; [exfalso; elim H44; left; reflexivity|clear H44].
                solve_ObjsInvalid_trivial.
                apply H40.
                eapply getDir_excl_neq; [reflexivity|intuition solve_mesi|simpl; congruence].
              }
              { exfalso.
                pose proof (getDir_setDirS_sound cidx0 [rcidx]).
                simpl in *; solve_mesi.
              }
            }
          }

          { pose proof Hpmcf as Hpmcf'; phide Hpmcf'; rename H39 into Hpmcf'.
            disc_MsgConflictsInv oidx.
            remember (dir_excl _) as rcidx; clear Heqrcidx.
            disc_AtomicMsgOutsInv rcidx.

            (** TODO: Ltac [derive_child_st rcidx] *)
            pose proof (tree2Topo_li_child_li_l1 _ _ _ (tl_In _ _ H8) H30).
            pose proof (Hosi _ H50); simpl in H51.
            destruct H51 as [[rcost ?] [rcorq ?]].
            disc_MsgPred.
            rewrite H51 in H48; simpl in H48; dest.
            preveal Hpmcf'; disc_MsgConflictsInv rcidx.
            
            disc_InvExcl_others.
            { disc_InvObjExcl0.
              exfalso.
              case_idx_eq eidx rcidx.
              { disc_rule_conds; disc_ObjExcl0; solve_mesi. }
              { solve_by_ObjsInvalid_downRsS_false rcidx. }
            }
            { case_in_subtree rcidx eidx;
                [|disc_InvObjOwned; solve_by_ObjsInvalid_downRsS_false rcidx].
              case_idx_eq eidx rcidx;
                [disc_rule_conds; disc_InvObjOwned; congruence|].
              disc_InvObjOwned.
              (* Too complicated to put in [solve_by_topo_false]? *)
              assert (In oidx (subtreeIndsOf (fst (tree2Topo tr 0)) eidx)).
              { eapply inside_parent_in with (cidx:= rcidx); eauto. }
              solve_ObjsInvalid_trivial.
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
                (* Too complicated to put in [solve_by_topo_false]? *)
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
        disc_MesiUpLockInv oidx.
        derive_child_chns cidx.
        disc_MsgConflictsInv oidx.
        disc_rule_conds_ex.

        split.
        { solve_AtomicInv_rsDown.
          disc_AtomicMsgOutsInv oidx.
          disc_MsgPred.
          disc_InvExcl oidx.
          solve_msg_pred_base.
          solve_ObjsInvalid_trivial.
          eapply ObjsInvalid_rsM; eauto.
          { apply tl_In; assumption. }
          { apply H27. }
        }
        { solve_InvExcl_trivial.
          case_InvExcl_me_others.
          { disc_InvExcl_this.
            { solve_InvObjExcl0_by_ObjExcl0_false. }
            { solve_InvObjOwned_by_false. }
            { pose proof H37.
              split_InvDirInv.
              { case_idx_eq cidx cidx0; [disc_dir; discriminate|].
                specialize (H44 (getDir_st_I _ H27 _)).
                solve_ObjsInvalid_trivial.
              }
              { case_idx_eq cidx cidx0; [|disc_dir; solve_mesi].
                disc_AtomicMsgOutsInv oidx.
                disc_MsgPred.
                solve_ObjsInvalid_trivial.
                eapply ObjsInvalid_rsM; eauto.
                apply H27.
              }
            }
          }

          { disc_InvExcl_others.
            { disc_InvObjExcl0.
              solve_by_ObjsInvalid_rsM_false oidx.
            }
            { case_InvObjOwned; [solve_by_ObjsInvalid_rsM_false oidx|].
              disc_ObjsInvalid_by oidx0; case_ObjInvalid.
              { case_idx_eq oidx0 cidx; [|solve_ObjInvalid0].
                eapply outside_parent_out in H46; eauto.
                solve_by_ObjsInvalid_rsM_false oidx.
              }
              { solve_ObjInvRs. }
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
          apply in_map_iff in H3; dest; subst.
          repeat constructor; try (red; simpl; intros; intuition discriminate).
        }
        { solve_InvExcl_trivial.
          case_InvExcl_me_others.
          { disc_InvExcl_this.
            { disc_InvObjExcl0; split.
              { solve_ObjsInvalid_trivial. }
              { solve_MsgsP. }
            }
            { disc_AtomicMsgOutsInv oidx.
              disc_MsgPred.
              red; intros _.
              solve_ObjsInvalid_trivial.
            }
            { split_InvDirInv_apply.
              { solve_ObjsInvalid_trivial. }
              { simpl in H35.
                pose proof (getDir_st_sound (fst (snd (snd (snd os)))) cidx0 ltac:(solve_mesi)).
                solve_mesi.
              }
            }
          }

          { disc_InvExcl_others.
            { disc_InvObjExcl0.
              solve_by_ObjsInvalid_rsM_false oidx.
            }
            { case_InvObjOwned.
              { solve_by_ObjsInvalid_rsM_false oidx. }
              { disc_ObjsInvalid_by oidx0.
                case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
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

      { (* [liDownIRsUpDown] *)
        (** TODOs:
         ** 1) Invariant for DL(mesiRqM): [rss] are from [dir >= S], others [dir = I].
         ** 2) Predicate message for downRsI(C): ObjsInvalid tr(C). 
         *)
        admit.
      }

      { (* [liDownIImm] *)
        disc_rule_conds_ex.
        split.
        { solve_AtomicInv_rqDown_rsUp.
          solve_msg_pred_base.

          disc_MsgConflictsInv oidx0.
          (** TODO: Ltac for discharging [InvExcl] *)
          repeat
            match goal with
            | [H: InvExcl _ _ _ |- _] => specialize (H oidx0); simpl in H
            | [He: _ <+- ?ov; _, Ho: ?ov = Some _ |- _] =>
              rewrite Ho in He; simpl in He; dest; repeat ssplit
            end.

          eapply ObjsInvalid_downRsI; eauto.
          { apply tl_In; assumption. }
          { apply H24. }
        }
        { solve_InvExcl_trivial.
          eapply InvExcl_state_transition_sound; try eassumption.
          { simpl; auto. }
          { simpl; intuition. }
          { reflexivity. }
        }
      }

      { (* [liDownIRqDownDownDirS] *)
        disc_rule_conds_ex; split.
        {

          Ltac solve_AtomicInv_rqDown_rqDowns' :=
            match goal with
            | [Hr: Reachable _ _ ?st,
                   Hs: steps _ _ ?st ?hst _,
                       Ha: Atomic _ _ _ ?hst _ ?eouts,
                           H: FirstMPI _ (?midx, ?msg)
               |- context [deqMP ?midx _] ] =>
              do 2 red; simpl;
              apply Forall_app;
              [change midx with (idOf (midx, msg)) at 1;
               eapply atomic_rqDown_rqDowns_preserves_msg_out_preds;
               try exact Hr; eauto; [red; auto; fail|]
              |repeat constructor;
               try (red; simpl; intros; intuition discriminate)]
            end.

            solve_AtomicInv_rqDown_rqDowns'.
            { apply Forall_forall; intros.
              apply in_map_iff in H14; dest; subst.
              apply in_map_iff in H15; dest; subst.
              apply H24 in H15.
              apply subtreeChildrenIndsOf_parentIdxOf in H15; auto.
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

      { (* [liDownIRqDownDownDirME] *)
        disc_rule_conds_ex; split.
        { solve_AtomicInv_rqDown_rqDowns.
          remember (dir_excl _) as cidx; clear Heqcidx.
          apply subtreeChildrenIndsOf_parentIdxOf in H24; auto.
          derive_child_chns cidx.
          repeat constructor; simpl; eauto.
        }
        { solve_InvExcl_trivial. }
      }

      { (* [liDownIRsUpUp] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx; [solve_midx_false|].
        split.
        { admit_msg_pred. }
        { solve_InvExcl_trivial.
          admit.
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
            { disc_InvObjExcl0; split.
              { eapply ObjsInvalid_invRs; eauto. }
              { solve_MsgsP. }
            }
            { case_InvObjOwned.
              { left.
                red; simpl; split; [solve_mesi|].
                eapply NoCohMsgs_rsDown_deq; eauto.
              }
              { disc_ObjsInvalid_by oidx0.
                case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
              }
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
          { simpl; intuition solve_mesi. }
          { simpl; intuition. }
          { reflexivity. }
        }
      }

    - (*! Cases for L1 caches *)
      apply in_map_iff in H7; destruct H7 as [oidx [? ?]]; subst.

      pose proof (c_l1_indices_has_parent Htr _ _ H8).
      destruct H7 as [pidx [? ?]].
      pose proof (Htn _ _ H10); dest.

      (** The object index does not belong to [c_li_indices]. *)
      assert (~ In oidx (c_li_indices (snd (tree2Topo tr 0)))) as Hnli.
      { pose proof (tree2Topo_WfCIfc tr 0) as [? _].
        apply (DisjList_NoDup idx_dec) in H15.
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
            { case_InvObjOwned; [solve_by_topo_false|].
              { disc_ObjsInvalid_by oidx0.
                case_ObjInvalid_with (l1ExtOf oidx).
                { solve_by_topo_false. }
                { case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs]. }
              }
            }
            { red; intros; exfalso; auto. }
          }

          { disc_InvExcl_others.
            { disc_InvObjExcl0.
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
      
      { (* [l1GetSRsDownDownE] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        derive_NoRsI_by_rsDown oidx msgs.

        split.
        { solve_AtomicInv_rsDown. }
        { solve_InvExcl_trivial.
          case_InvExcl_me_others.
          { disc_AtomicMsgOutsInv oidx.
            disc_MsgPred.
            disc_InvExcl_this.
            { red; intros; split.
              { solve_ObjsInvalid_trivial. }
              { disc_MsgConflictsInv oidx.
                eapply NoCohMsgs_rsDown_deq; eauto.
              }
            }
            { disc_InvObjOwned; solve_ObjsInvalid_trivial. }
            { red; intros; exfalso; auto. }
          }
          
          { disc_InvExcl_others.
            { disc_InvObjExcl0.
              disc_MsgConflictsInv oidx.
              solve_by_ObjsInvalid_rsE_false oidx.
            }
            { case_InvObjOwned.
              { disc_MsgConflictsInv oidx.
                solve_by_ObjsInvalid_rsE_false oidx.
              }
              { disc_ObjsInvalid_by oidx0.
                case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
              }
            }
            { split_InvDirInv_apply.
              { case_in_subtree oidx cidx.
                { disc_MsgConflictsInv oidx.
                  solve_by_ObjsInvalid_rsE_false oidx.
                }                  
                { solve_ObjsInvalid_trivial. }
              }
              { case_in_subtree oidx cidx.
                { solve_ObjsInvalid_trivial. }
                { disc_MsgConflictsInv oidx.
                  solve_by_ObjsInvalid_rsE_false oidx.
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
          simpl; intuition solve_mesi.
        }
        { case_InvExcl_me_others.
          { disc_InvExcl_this.
            { solve_InvObjExcl0_by_ObjExcl0_false. }
            { solve_InvObjOwned_by_false. }
            { red; intros; exfalso; auto. }
          }
          { disc_InvExcl_others.
            { disc_InvObjExcl0.
              solve_by_ObjsInvalid_status_false oidx.
            }
            { case_InvObjOwned; [solve_by_ObjsInvalid_status_false oidx|].
              disc_ObjsInvalid_by oidx0.
              case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
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

      { (* [l1GetMImmE] *)
        disc_rule_conds_ex; exfalso; disc_AtomicMsgOutsInv (l1ExtOf oidx); eauto.
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
        { solve_InvExcl_trivial.
          disc_AtomicMsgOutsInv oidx.
          disc_MsgPred.
          
          case_InvExcl_me_others.
          { disc_InvExcl_this.
            { red; intros; split.
              { solve_ObjsInvalid_trivial. }
              { disc_MsgConflictsInv oidx.
                eapply NoCohMsgs_rsDown_deq; eauto.
              }
            }
            { red; simpl; intros.
              solve_ObjsInvalid_trivial.
            }
            { red; intros; exfalso; auto. }
          }

          { apply ObjsInvalid_shrinked in H34; [|eassumption..].
            disc_InvExcl_others.
            { disc_InvObjExcl0.
              disc_ObjExcl0.
              solve_by_ObjsInvalid_status_false eidx.
            }
            { case_InvObjOwned.
              { disc_MsgConflictsInv oidx.
                solve_by_ObjsInvalid_rsM_false oidx.
              }
              { disc_ObjsInvalid_by oidx0.
                case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
              }
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

      { (* [l1DownIImm] *)
        disc_rule_conds_ex.
        derive_NoRsI_by_rqDown oidx msgs.
        
        split.
        { disc_MsgConflictsInv oidx.
          solve_AtomicInv_rqDown_rsUp.
          solve_msg_pred_base.
          eapply ObjsInvalid_l1_singleton; eauto; mred.
          left; split; simpl; [solve_mesi|].
          apply NoCohMsgs_enq; [|solve_not_in].
          eapply NoCohMsgs_rqDown_deq; eauto.
        }
        { case_InvExcl_me_others.
          { disc_InvExcl_this.
            { solve_InvObjExcl0_by_ObjExcl0_false. }
            { solve_InvObjOwned_by_false. }
            { red; intros; exfalso; auto. }
          }
          { disc_InvExcl_others.
            { disc_InvObjExcl0.
              solve_by_ObjsInvalid_status_false oidx.
            }
            { case_InvObjOwned; [solve_by_ObjsInvalid_status_false oidx|].
              disc_ObjsInvalid_by oidx0.
              case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
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
            { disc_InvObjExcl0; split.
              { eapply ObjsInvalid_invRs; eauto. }
              { solve_MsgsP. }
            }
            { case_InvObjOwned.
              { left.
                red; simpl; split; [solve_mesi|].
                eapply NoCohMsgs_rsDown_deq; eauto.
              }
              { disc_ObjsInvalid_by oidx0.
                case_ObjInvalid; [solve_ObjInvalid0|solve_ObjInvRs].
              }
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

      Unshelve.
      all: assumption.

  Qed.

  Lemma mesi_InvExcl_step:
    InvStep impl step_m (InvExcl topo cifc).
  Proof.
    apply invSeq_serializable_invStep.
    - apply mesi_InvExcl_init.
    - apply inv_trs_seqSteps.
      apply mesi_InvExcl_InvTrs.
    - eapply rqrs_Serializable.
      + apply mesi_GoodORqsInit.
      + apply mesi_RqRsSys.
  Qed.

  Lemma mesi_InvExcl_ok:
    Invariant.InvReachable impl step_m (InvExcl topo cifc).
  Proof.
    apply inv_reachable.
    - apply mesi_InvExcl_init.
    - apply mesi_InvExcl_step.
  Qed.

End InvExcl.

