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

(** TODO: move to the proper site. *)
Lemma rssQ_deq_in_length_two:
  forall msgs midx msg1,
    FirstMPI msgs (midx, msg1) ->
    msg_type msg1 = MRs ->
    forall msg2,
      InMP midx msg2 (deqMP midx msgs) ->
      msg_type msg2 = MRs ->
      List.length (rssQ msgs midx) >= 2.
Proof.
  cbv [FirstMPI FirstMP firstMP InMP rssQ deqMP]; simpl; intros.
  destruct (findQ midx msgs) as [|emsg q]; [discriminate|].
  simpl in *; inv H.
  rewrite H0; simpl.
  unfold findQ in H1; mred; simpl in H1.

  clear -H1 H2.
  induction q; intros; [dest_in|].
  inv H1.
  - simpl; rewrite H2; simpl; lia.
  - simpl; destruct (msg_type a).
    + simpl; lia.
    + apply IHq; assumption.
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

Definition InvExcl (topo: DTree) (st: MState): Prop :=
  forall eidx,
    eost <+- (bst_oss st)@[eidx];
      (InvObjExcl0 eidx eost (bst_oss st) (bst_msgs st) /\
       InvObjOwned topo eidx eost (bst_oss st) (bst_msgs st)).

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
    - destruct H8 as [rsUp [? ?]]; inv H8.
      apply H6 with (rsUp:= rsUp); auto.
      eapply InMP_deqMP; eauto.
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

  Lemma ObjsInvalid_this_deqMP_silent:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall roidx,
        ~ inP roidx ->
        ObjsInvalid inP oss (deqMP (downTo roidx) msgs).
  Proof.
    intros.
    red; intros.
    specialize (H _ H1).
    destruct (oss@[oidx]) as [ost|]; simpl in *; auto.
    destruct H.
    - left.
      destruct H.
      split; [assumption|solve_MsgsP].
    - right.
      destruct H as [[midx msg] [? ?]]; inv H2.
      exists (downTo oidx, msg); split.
      + apply deqMP_InMP_midx; [assumption|].
        simpl; intro Hx; inv Hx; auto.
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

End Facts.

Ltac disc_ObjExcl0_msgs H :=
  repeat
    (first [apply ObjExcl0_enqMP_inv in H
           |apply ObjExcl0_enqMsgs_inv in H
           |apply ObjExcl0_other_midx_deqMP_inv in H;
            [|solve_chn_neq; fail]
           |apply ObjExcl0_other_midx_deqMsgs_inv in H;
            [|eassumption|eassumption|] (** FIXME: need to debug when not working *)
           |eapply ObjExcl0_other_msg_id_deqMP_inv in H;
            [|eassumption
             |simpl; try match goal with
                         | [H: ?lh = _ |- ?lh <> _] => rewrite H
                         end; discriminate]
           |eapply ObjExcl0_other_msg_id_deqMsgs_inv in H;
            [|eassumption|eassumption|] (** FIXME: need to debug when not working *)
    ]).

Section InvExcl.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma mesi_InvExcl_init:
    Invariant.InvInit impl (InvExcl topo).
  Proof.
    do 2 (red; simpl); intros.
    destruct (implOStatesInit tr)@[eidx] as [eost|] eqn:Heost; simpl; auto.
    split.

    - red; intros.
      red in H; dest.
      destruct (in_dec idx_dec eidx (c_li_indices cifc ++ c_l1_indices cifc)).
      + subst cifc; rewrite c_li_indices_head_rootOf in i by assumption.
        inv i.
        * split.
          { red; intros.
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
          }
          { do 3 red; intros; do 2 red in H1; dest_in. }
        * exfalso.
          rewrite implOStatesInit_value_non_root in Heost by assumption.
          inv Heost.
          simpl in *; solve_mesi.
      + exfalso.
        rewrite implOStatesInit_None in Heost by assumption.
        discriminate.

    - red; intros.
      destruct (in_dec idx_dec eidx (c_li_indices cifc ++ c_l1_indices cifc)).
      + subst cifc; rewrite c_li_indices_head_rootOf in i by assumption.
        inv i.
        * red; intros.
          destruct (implOStatesInit tr)@[oidx] as [ost|] eqn:Host; simpl; auto.
          red.
          destruct (in_dec idx_dec oidx ((c_li_indices (snd (tree2Topo tr 0)))
                                           ++ c_l1_indices (snd (tree2Topo tr 0)))).
          { rewrite c_li_indices_head_rootOf in i by assumption.
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
          }
          { rewrite implOStatesInit_None in Host by assumption; discriminate. }
        * rewrite implOStatesInit_value_non_root in Heost by assumption.
          inv Heost; discriminate.
      + rewrite implOStatesInit_None in Heost by assumption; discriminate.
  Qed.

  Lemma mesi_InvExcl_ext_in:
    forall oss orqs msgs,
      InvExcl topo {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        InvExcl topo {| bst_oss := oss;
                        bst_orqs := orqs;
                        bst_msgs := enqMsgs eins msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.
    dest; split.

    - clear H2.
      red; intros.
      destruct H2.
      apply MsgsP_enqMsgs_inv in H3.
      specialize (H (conj H2 H3)); dest.

      split.
      + red; intros.
        specialize (H _ H5).
        destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
        destruct H.
        * left.
          red in H; dest.
          repeat split; [assumption..|].
          apply MsgsP_other_midx_enqMsgs; [assumption|].
          destruct H1; simpl.
          eapply DisjList_SubList; [eassumption|].
          eapply DisjList_comm, DisjList_SubList.
          { eapply SubList_trans;
              [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= oidx)].
            { solve_SubList. }
            { specialize (H0 oidx); simpl in H0.
              rewrite Host in H0; simpl in H0.
              eassumption.
            }
          }
          { apply tree2Topo_minds_merqs_disj. }
        * right.
          destruct H as [idm ?]; dest.
          exists idm; split; [|assumption].
          apply InMP_or_enqMsgs; auto.

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

    - clear H.
      red; intros.
      specialize (H2 H).

      red; intros.
      specialize (H2 _ H3).
      destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
      destruct H2.
      + left.
        red in H2; dest.
        repeat split; [assumption..|].
        apply MsgsP_other_midx_enqMsgs; [assumption|].
        destruct H1; simpl.
        eapply DisjList_SubList; [eassumption|].
        eapply DisjList_comm, DisjList_SubList.
        * eapply SubList_trans;
            [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= oidx)].
          { solve_SubList. }
          { specialize (H0 oidx); simpl in H0.
            rewrite Host in H0; simpl in H0.
            eassumption.
          }
        * apply tree2Topo_minds_merqs_disj.
      + right.
        destruct H2 as [idm ?]; dest.
        exists idm; split; [|assumption].
        apply InMP_or_enqMsgs; auto.
  Qed.

  Corollary mesi_InvExcl_InvTrsIns: InvTrsIns impl (InvExcl topo).
  Proof.
    red; intros.
    inv H1.
    eapply mesi_InvExcl_ext_in; eauto.
    apply (mesi_InObjInds H).
  Qed.

  Lemma mesi_InvExcl_ext_out:
    forall oss orqs msgs,
      InvExcl topo {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall (eouts: list (Id Msg)),
        ValidMsgsExtOut impl eouts ->
        InvExcl topo {| bst_oss := oss;
                        bst_orqs := orqs;
                        bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    destruct (oss@[eidx]) as [eost|] eqn:Heost; simpl in *; auto.
    dest; split.

    - clear H2.
      red; intros.
      destruct H2.
      apply MsgsP_other_midx_deqMsgs_inv in H3.
      + specialize (H (conj H2 H3)); dest.
        split.
        * red; intros.
          specialize (H _ H5).
          destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
          destruct H.
          { left.
            red in H; dest.
            repeat split; [assumption..|].
            apply MsgsP_deqMsgs; assumption.
          }
          { right.
            destruct H as [idm ?]; dest.
            exists idm; split; [|assumption].
            apply deqMsgs_InMP_midx; [assumption|].
            destruct H1.
            eapply DisjList_In_1.
            { eapply DisjList_SubList; [eassumption|].
              apply DisjList_comm, tree2Topo_minds_merss_disj.
            }
            { eapply tree2Topo_obj_chns_minds_SubList with (oidx:= oidx).
              { specialize (H0 oidx); simpl in H0.
                rewrite Host in H0; simpl in H0.
                eassumption.
              }
              { inv H6; rewrite H9.
                solve_SubList.
              }
            }
          }
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

    - clear H.
      red; intros.
      specialize (H2 H).
      red; intros.
      specialize (H2 _ H3).
      destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
      destruct H2.
      + left.
        red in H2; dest.
        repeat split; [assumption..|].
        apply MsgsP_deqMsgs; assumption.
      + right.
        destruct H2 as [idm ?]; dest.
        exists idm; split; [|assumption].
        apply deqMsgs_InMP_midx; [assumption|].
        destruct H1.
        eapply DisjList_In_1.
        { eapply DisjList_SubList; [eassumption|].
          apply DisjList_comm, tree2Topo_minds_merss_disj.
        }
        { eapply tree2Topo_obj_chns_minds_SubList with (oidx:= oidx).
          { specialize (H0 oidx); simpl in H0.
            rewrite Host in H0; simpl in H0.
            eassumption.
          }
          { inv H4; rewrite H7.
            solve_SubList.
          }
        }
  Qed.

  Corollary mesi_InvExcl_InvTrsOuts: InvTrsOuts impl (InvExcl topo).
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

  Definition RsMEPred (oidx: IdxT) (eout: Id Msg) (oss: OStates)
             (msgs: MessagePool Msg): Prop :=
    idOf eout = downTo oidx ->
    (valOf eout).(msg_type) = MRs ->
    ((valOf eout).(msg_id) = mesiRsM \/ (valOf eout).(msg_id) = mesiRsE) ->
    ObjsInvalid (fun idx => ~ In idx (subtreeIndsOf topo oidx)) oss msgs.

  Definition InvExclMsgOutPred: MsgOutPred :=
    fun eout oss orqs msgs =>
      forall oidx,
        GetRqPred oidx eout /\ SetRqPred oidx eout /\
        RsMEPred oidx eout oss msgs.

  Lemma InvExclMsgOutPred_good:
    GoodMsgOutPred topo InvExclMsgOutPred.
  Proof.
  Admitted.

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

  Ltac disc_rule_custom ::=
    try disc_AtomicInv.

  (*! Ltacs about [InvExcl] *)

  Ltac case_InvExcl_me_others :=
    match goal with
    | |- InvExcl _ _ => red; simpl; intros; mred; simpl
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

  Ltac disc_InvExcl_this :=
    repeat
      match goal with
      | [H: InvExcl _ _ |- InvObjExcl0 ?oidx _ _ _ /\ _] =>
        specialize (H oidx); simpl in H
      | [He: _ <+- ?ov; _, Ho: ?ov = Some _ |- _] =>
        rewrite Ho in He; simpl in He; dest; split
      end.

  Ltac disc_InvExcl_others :=
    match goal with
    | [H: InvExcl _ _ |- _ <+- _@[?eidx]; _] =>
      specialize (H eidx); simpl in H;
      disc_bind_true; dest; split
    end.

  Ltac disc_ObjsInvalid oidx :=
    match goal with
    | [Hi: ObjsInvalid _ _ _ |- _] =>
      specialize (Hi oidx ltac:(auto)); disc_bind_true
    end.

  Ltac disc_InvObjExcl0 :=
    match goal with
    | [H: InvObjExcl0 _ _ _ _ |- InvObjExcl0 _ _ _ _] =>
      let He := fresh "H" in
      red; intros He; disc_ObjExcl0_msgs He;
      specialize (H He); dest
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
    try subst topo;
    match goal with
    | [H: ~ In ?oidx (subtreeIndsOf _ ?oidx) |- _] =>
      elim H; eapply parent_subtreeIndsOf_self_in; eauto; fail
    | [H: ~ In ?oidx (subtreeIndsOf _ ?oidx) |- _] =>
      elim H; eapply rqEdgeUpFrom_subtreeIndsOf_self_in; eauto; congruence
    | [Hp: parentIdxOf _ ?cidx = Some ?pidx, Hi: ~ In ?cidx (subtreeIndsOf _ ?oidx) |- _] =>
      elim Hi; apply subtreeIndsOf_child_in; auto; fail
    | [Hp: parentIdxOf _ ?cidx = Some ?pidx, Hip: In ?pidx (subtreeIndsOf _ ?oidx), Hic: ~ In ?cidx (subtreeIndsOf _ ?oidx) |- _] =>
      elim Hic; eapply inside_child_in; eauto; fail
    end.

  Ltac solve_ObjInvalid0 :=
    match goal with
    | [H: ObjInvalid0 _ _ _ |- ObjInvalid0 _ _ _] =>
      destruct H; split; [assumption|solve_MsgsP]
    end.

  Ltac solve_ObjInvRs :=
    match goal with
    | [H: ObjInvRs _ _ |- ObjInvRs _ _] =>
      let midx := fresh "midx" in
      let msg := fresh "msg" in
      destruct H as [[midx msg] [? ?]];
      exists (midx, msg); split; [|assumption]
    end.

  Ltac solve_by_ObjsInvalid_false roidx :=
    exfalso;
    eapply ObjsInvalid_obj_status_false with (oidx:= roidx); eauto;
    simpl in *; solve_mesi.

  Ltac solve_InvObjOwned_by_false :=
    red; simpl; intros; discriminate.

  Lemma ObjsInvalid_deq_sound:
    forall inP oss msgs,
      ObjsInvalid inP oss msgs ->
      forall rmsgs,
        NoDup (idsOf rmsgs) ->
        Forall (FirstMPI msgs) rmsgs ->
        Forall (fun idm => In (msg_id (valOf idm))
                              [mesiRqS; mesiDownRqS;
                                 mesiRqM; mesiDownRqI;
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
      inv H5.
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
                                 mesiRqM; mesiDownRqI;
                                   mesiInvRq; mesiInvWRq;
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
      InvExcl topo {| bst_oss := oss; bst_orqs := porqs; bst_msgs := msgs |} ->
      forall rmsgs,
        NoDup (idsOf rmsgs) ->
        Forall (FirstMPI msgs) rmsgs ->
        Forall (fun idm => In (msg_id (valOf idm))
                              [mesiRqS; mesiDownRqS;
                                 mesiRqM; mesiDownRqI;
                                   mesiInvRq; mesiInvWRq;
                                     getRq; getRs; setRq; setRs]) rmsgs ->
        InvExcl topo {| bst_oss := oss;
                        bst_orqs := norqs;
                        bst_msgs := deqMsgs (idsOf rmsgs) msgs |}.
  Proof.
    intros.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    disc_bind_true; dest; split.
    - red; intros.
      destruct H5.
      apply MsgsP_other_msg_id_deqMsgs_inv in H6; try assumption.
      + specialize (H (conj H5 H6)); dest; split.
        * apply ObjsInvalid_deq_sound; auto.
        * solve_MsgsP.
      + simpl.
        apply (DisjList_spec_1 idx_dec); intros midx ?.
        apply in_map_iff in H7; destruct H7 as [[rmidx msg] [? ?]].
        simpl in *; subst.
        rewrite Forall_forall in H2; specialize (H2 _ H8); simpl in H2.
        intro Hx; destruct Hx; [|auto].
        rewrite <-H7 in H2.
        intuition discriminate.
    - red; intros.
      specialize (H4 H5).
      apply ObjsInvalid_deq_sound; auto.
  Qed.

  Lemma InvExcl_enq_sound:
    forall oss porqs norqs msgs,
      InvExcl topo {| bst_oss := oss; bst_orqs := porqs; bst_msgs := msgs |} ->
      forall nmsgs,
        Forall (fun idm => In (msg_id (valOf idm))
                              [mesiRqS; mesiDownRqS;
                                 mesiRqM; mesiDownRqI;
                                   mesiInvRq; mesiInvWRq;
                                     getRq; getRs; setRq; setRs]) nmsgs ->
        InvExcl topo {| bst_oss := oss;
                        bst_orqs := norqs;
                        bst_msgs := enqMsgs nmsgs msgs |}.
  Proof.
    intros.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    disc_bind_true; dest; split.
    - disc_InvObjExcl0; split.
      + apply ObjsInvalid_enq_sound; auto.
      + apply MsgsP_other_msg_id_enqMsgs; [assumption|].
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
    - red; intros.
      specialize (H2 H3).
      apply ObjsInvalid_enq_sound; auto.
  Qed.

  Lemma InvExcl_state_transition_sound:
    forall oss porqs msgs,
      InvExcl topo {| bst_oss := oss; bst_orqs := porqs; bst_msgs := msgs |} ->
      forall oidx (post nost: OState) norqs,
        oss@[oidx] = Some post ->
        nost#[status] <= post#[status] ->
        post#[owned] = nost#[owned] ->
        InvExcl topo {| bst_oss := oss +[oidx <- nost];
                        bst_orqs := norqs; bst_msgs := msgs |}.
  Proof.
    intros.
    red; simpl; intros.
    specialize (H eidx); simpl in H.
    mred; simpl; dest.
    - split.
      + red; intros.
        destruct H4.
        assert (mesiE <= post#[status]) by solve_mesi.
        specialize (H (conj H6 H5)); dest.
        split; [|assumption].
        red; intros; mred.
        apply H; assumption.
      + red; intros.
        setoid_rewrite <-H2 in H4.
        specialize (H3 H4).
        red; intros; specialize (H3 _ H5).
        mred; simpl; auto.
        destruct H3; [left|right; assumption].
        red in H3; dest.
        split; [|assumption].
        solve_mesi.
    - disc_bind_true; dest; split.
      + red; intros; specialize (H H5); dest.
        split; [|assumption].
        red; intros; specialize (H _ H7).
        mred; simpl; auto.
        destruct H; [left|right; assumption].
        red in H; dest.
        split; [|assumption].
        simpl in *; solve_mesi.
      + red; intros.
        specialize (H4 H5).
        red; intros; specialize (H4 _ H6).
        mred; simpl; auto.
        destruct H4; [left|right; assumption].
        red in H4; dest.
        split; [|assumption].
        simpl in *; solve_mesi.
  Qed.

  Ltac solve_InvExcl_trivial :=
    try
      match goal with
      | |- InvExcl _ {| bst_oss := ?oss +[?oidx <- ?pos] |} =>
        replace (oss +[oidx <- pos]) with oss by meq
      end;
    repeat
      match goal with
      | [He: InvExcl _ {| bst_orqs := ?orqs |}
         |- InvExcl _ {| bst_msgs := enqMP ?midx ?msg _ |}] =>
        eapply InvExcl_enq_sound
          with (porqs:= orqs) (nmsgs:= [(midx, msg)])
      | [He: InvExcl _ {| bst_orqs := ?orqs |},
             Hf: FirstMPI _ (?midx, ?msg)
         |- InvExcl _ {| bst_msgs := deqMP ?midx _ |}] =>
        eapply InvExcl_deq_sound
          with (porqs:= orqs) (rmsgs:= [(midx, msg)])
      | [He: InvExcl _ {| bst_orqs := ?orqs |}
         |- InvExcl _ {| bst_msgs := enqMsgs _ _ |}] =>
        eapply InvExcl_enq_sound with (porqs:= orqs)
      | [He: InvExcl _ {| bst_orqs := ?orqs |}
         |- InvExcl _ {| bst_msgs := deqMsgs _ _ |}] =>
        eapply InvExcl_deq_sound with (porqs:= orqs)
      end; try eassumption;
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
      | |- Forall _ (map _ _) =>
        let midx := fresh "midx" in
        let msg := fresh "msg" in
        let Hin := fresh "H" in
        apply Forall_forall; intros [midx msg] Hin;
        apply in_map_iff in Hin; dest
      | [H: (_, _) = (_, _) |- _] => inv H
      end.

  Ltac msg_pred_admit := admit.

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

  Ltac pick_disc_response_from :=
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

  Lemma mesi_InvExcl_InvTrs_init:
    forall st1,
      Reachable (steps step_m) impl st1 ->
      InvExcl topo st1 ->
      forall oidx ridx ins outs st2,
        SubList (idsOf ins) (sys_merqs impl) ->
        step_m impl st1 (RlblInt oidx ridx ins outs) st2 ->
        AtomicInv
          InvExclMsgOutPred
          ins st1 [RlblInt oidx ridx ins outs] outs st2 /\
        InvExcl topo st2.
  Proof.
    intros.

    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
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
        pick_disc_response_from.
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
        pick_disc_response_from.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }
      { disc_MesiDownLockInv oidx Hdlinv.
        derive_footprint_info_basis oidx; [solve_midx_false|].
        pick_disc_response_from.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        exfalso_InvTrs_init.
      }

      { (* [liInvRqUpUp] *)
        disc_rule_conds_ex; split.
        { msg_pred_admit. }
        { solve_InvExcl_trivial. }
      }

      { (* [liInvRqUpUpWB] *)
        disc_rule_conds_ex; split.
        { msg_pred_admit. }
        { solve_InvExcl_trivial. }
      }

      { (* [liPushImm] *)
        disc_rule_conds_ex; split.
        { msg_pred_admit. }
        { eapply InvExcl_state_transition_sound with (porqs:= orqs); eauto.
          simpl; intuition solve_mesi.
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
        { msg_pred_admit. }
        { solve_InvExcl_trivial. }
      }

      { (* [l1GetSRqUpUp] *)
        disc_rule_conds_ex; split.
        { msg_pred_admit. }
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
        assert (NoRsI oidx msgs).
        { solve_NoRsI_base.
          solve_NoRsI_by_no_uplock oidx.
        }

        split.
        { msg_pred_admit. }
        { solve_InvExcl_trivial.
          case_InvExcl_me_others.
          { assert (ObjExcl0 oidx os msgs)
              by (split; [simpl in *; solve_mesi|assumption]).
            disc_InvExcl_this.
            { specialize (H0 H9); dest.
              red; intros.
              split; [|assumption].
              red; intros; specialize (H0 _ H24); mred.
            }
            { specialize (H0 H9); dest.
              red; intros _.
              red; intros.
              mred; [solve_by_topo_false|auto].
            }
          }
          { disc_InvExcl_others.
            { disc_InvObjExcl0.
              solve_by_ObjsInvalid_false oidx.
            }
            { case_InvObjOwned.
              { solve_by_ObjsInvalid_false oidx. }
              { auto. }
            }
          }
        }
      }

      { (* [l1GetMImmM] *)
        disc_rule_conds_ex; split.
        { msg_pred_admit. }
        { eapply InvExcl_state_transition_sound with (porqs:= orqs); eauto.
          solve_InvExcl_trivial.
        }
      }

      { (* [l1GetMRqUpUp] *)
        disc_rule_conds_ex; split.
        { msg_pred_admit. }
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
        { msg_pred_admit. }
        { solve_InvExcl_trivial. }
      }
      
      { (* [l1InvRqUpUpWB] *)
        disc_rule_conds_ex; split.
        { msg_pred_admit. }
        { solve_InvExcl_trivial. }
      }
      
      { (* [l1InvRsDownDown] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        exfalso_InvTrs_init.
      }

      Unshelve.
      all: assumption.
  Qed.
  
  Lemma mesi_InvExcl_InvTrs: InvTrs impl (InvExcl topo).
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

    inv_steps.
    pose proof (reachable_steps H H9) as Hr1.
    pose proof (reachable_steps Hr1 (steps_singleton H11)) as Hr2.

    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) Hr1) as Hftinv.
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

        dest_in.

        { (* [liGetSImmS] *)
          disc_rule_conds_ex.

          assert (NoRsI oidx msgs).
          { solve_NoRsI_base.
            solve_NoRsI_by_no_uplock oidx.
          }
          
          split.
          { msg_pred_admit. }
          { case_InvExcl_me_others.
            { disc_InvExcl_this.
              { solve_InvObjExcl0_by_ObjExcl0_false. }
              { case_InvObjOwned.
                { solve_by_topo_false. }
                { disc_ObjsInvalid oidx0.
                  case_ObjInvalid_with cidx.
                  { solve_by_topo_false. }
                  { case_ObjInvalid.
                    { solve_ObjInvalid0. }
                    { solve_ObjInvRs.
                      inv H27.
                      apply InMP_or_enqMP; right.
                      apply deqMP_InMP_midx; [|solve_chn_not_in].
                      assumption.
                    }
                  }
                }
              }
            }

            { disc_InvExcl_others.
              { disc_InvObjExcl0.
                solve_by_ObjsInvalid_false oidx.
              }
              { case_InvObjOwned.
                { solve_by_ObjsInvalid_false oidx. }
                { derive_not_InvalidObj_not_in oidx.
                  disc_ObjsInvalid oidx0.
                  case_ObjInvalid_with cidx.
                  { solve_by_topo_false. }
                  { case_ObjInvalid.
                    { solve_ObjInvalid0. }
                    { solve_ObjInvRs.
                      inv H29.
                      apply InMP_or_enqMP; right.
                      apply deqMP_InMP_midx; [|solve_chn_not_in].
                      assumption.
                    }
                  }
                }
              }
            }
          }
        }

        { (* [liGetSImmME] *)
          disc_rule_conds_ex.

          assert (NoRsI oidx msgs).
          { solve_NoRsI_base.
            solve_NoRsI_by_no_uplock oidx.
          }

          split.
          { msg_pred_admit. }
          { case_InvExcl_me_others.
            { disc_InvExcl_this.
              { solve_InvObjExcl0_by_ObjExcl0_false. }
              { case_InvObjOwned.
                { solve_by_topo_false. }
                { disc_ObjsInvalid oidx0.
                  case_ObjInvalid_with cidx.
                  { solve_by_topo_false. }
                  { case_ObjInvalid.
                    { solve_ObjInvalid0. }
                    { solve_ObjInvRs.
                      inv H27.
                      apply InMP_or_enqMP; right.
                      apply deqMP_InMP_midx; [|solve_chn_not_in].
                      assumption.
                    }
                  }
                }
              }
            }

            { disc_InvExcl_others.
              { disc_InvObjExcl0.
                solve_by_ObjsInvalid_false oidx.
              }
              { case_InvObjOwned.
                { solve_by_ObjsInvalid_false oidx. }
                { derive_not_InvalidObj_not_in oidx.
                  disc_ObjsInvalid oidx0.
                  case_ObjInvalid_with cidx.
                  { solve_by_topo_false. }
                  { case_ObjInvalid.
                    { solve_ObjInvalid0. }
                    { solve_ObjInvRs.
                      inv H29.
                      apply InMP_or_enqMP; right.
                      apply deqMP_InMP_midx; [|solve_chn_not_in].
                      assumption.
                    }
                  }
                }
              }
            }
          }
        }

        { (* [liGetSRqUpDownME] *)
          disc_rule_conds_ex; split.
          { msg_pred_admit. }
          { solve_InvExcl_trivial. }
        }

        { (* [liGetMImm] *) admit. }

        { (* [liGetMRqUpDownME] *)
          disc_rule_conds_ex; split.
          { msg_pred_admit. }
          { solve_InvExcl_trivial. }
        }
        { (* [liGetMRqUpDownS] *)
          disc_rule_conds_ex; split.
          { msg_pred_admit. }
          { solve_InvExcl_trivial. }
        }

        { (* [liInvImmI] *) admit. }
        { (* [liInvImmS0] *) admit. }
        { (* [liInvImmS1] *) admit. }
        { (* [liInvImmE] *) admit. }
        { (* [liInvImmWBI] *) admit. }
        { (* [liInvImmWBS1] *) admit. }
        { (* [liInvImmWBME] *) admit. }
        
      }

      dest_in.
      all: admit.

    - (*! Cases for Li caches *)
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

        dest_in.
        all: admit.
      }

      dest_in.
      all: admit.

    - (*! Cases for L1 caches *)
      apply in_map_iff in H7; destruct H7 as [oidx [? ?]]; subst.

      pose proof (c_l1_indices_has_parent Htr _ _ H8).
      destruct H7 as [pidx [? ?]].
      pose proof (Htn _ _ H10); dest.

      (** Discharge an invariant that holds only for L1 caches. *)
      (* red in Hl1d; simpl in Hl1d. *)
      (* rewrite Forall_forall in Hl1d; specialize (Hl1d _ H2). *)
      (* simpl in H5; rewrite H5 in Hl1d; simpl in Hl1d. *)

      (** Do case analysis per a rule. *)
      dest_in.

      { (* [l1GetSImm] *)
        disc_rule_conds_ex.
        exfalso.
        Ltac disc_AtomicMsgOutsInv oidx :=
          match goal with
          | [Ha: AtomicMsgOutsInv _ ?eouts _, Hin: In _ ?eouts |- _] =>
            red in Ha; rewrite Forall_forall in Ha; specialize (Ha _ Hin oidx);
            simpl in Ha; dest
          end.

        disc_AtomicMsgOutsInv (l1ExtOf oidx).
        eauto.
      }

      { (* [l1GetSRqUpUp] *)
        disc_rule_conds_ex.
        exfalso; disc_AtomicMsgOutsInv (l1ExtOf oidx); eauto.
      }

      { (* [l1GetSRsDownDownS] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.

        split.
        { msg_pred_admit. }
        { (** TODO: from [solve_InvExcl_trivial] *)
          match goal with
          | [He: InvExcl _ {| bst_orqs := ?orqs |}
             |- InvExcl _ {| bst_msgs := enqMP ?midx ?msg _ |}] =>
            eapply InvExcl_enq_sound
              with (porqs:= orqs) (nmsgs:= [(midx, msg)])
          end.
          2: {
            constructor; [|constructor].
            simpl; tauto.
          }
          
          case_InvExcl_me_others.
          { disc_InvExcl_this.
            { solve_InvObjExcl0_by_ObjExcl0_false. }
            { case_InvObjOwned.
              { (* solve_by_topo_false. *)
                elim H34.
                eapply rqEdgeUpFrom_subtreeIndsOf_self_in; eauto.
                (** TODO: well this unfold is not good at all *)
                unfold InvExclMsgOutPred, RsMEPred in *.
                subst topo; rewrite H11; discriminate.
              }
              { disc_ObjsInvalid oidx0.
                case_ObjInvalid_with (l1ExtOf oidx).
                { (* solve_by_topo_false. *)
                  elim H34.
                  apply subtreeIndsOf_child_in; auto.
                  apply tree2Topo_l1_ext_parent; assumption.
                }
                { case_ObjInvalid.
                  { solve_ObjInvalid0. }
                  { solve_ObjInvRs.
                    inv H36.
                    apply deqMP_InMP_midx; [|solve_chn_not_in].
                    assumption.
                  }
                }
              }
            }
          }

          { disc_InvExcl_others.
            { disc_InvObjExcl0.
              (* solve_by_ObjsInvalid_false oidx. *)
              disc_MsgConflictsInv oidx.
              exfalso.
              eapply ObjsInvalid_rsS_false with (oidx:= oidx); eauto.
              apply FirstMP_InMP; assumption.
            }
            { case_InvObjOwned.
              { (* solve_by_ObjsInvalid_false oidx. *)
                disc_MsgConflictsInv oidx.
                exfalso.
                eapply ObjsInvalid_rsS_false with (oidx:= oidx); eauto.
                apply FirstMP_InMP; assumption.
              }
              { disc_ObjsInvalid oidx0.
                case_ObjInvalid.
                { solve_ObjInvalid0. }
                { solve_ObjInvRs.
                  inv H37.
                  apply deqMP_InMP_midx; [|solve_chn_not_in].
                  assumption.
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

        assert (NoRsI oidx msgs).
        { solve_NoRsI_base.
          solve_NoRsI_by_rsDown oidx.
        }

        split.
        { msg_pred_admit. }
        { (** TODO: from [solve_InvExcl_trivial] *)
          match goal with
          | [He: InvExcl _ {| bst_orqs := ?orqs |}
             |- InvExcl _ {| bst_msgs := enqMP ?midx ?msg _ |}] =>
            eapply InvExcl_enq_sound
              with (porqs:= orqs) (nmsgs:= [(midx, msg)])
          end.
          2: {
            constructor; [|constructor].
            simpl; tauto.
          }

          case_InvExcl_me_others.
          { (* discharge [AtomicMsgOutsInv] *)
            move H5 at bottom.
            red in H5.
            rewrite Forall_forall in H5; specialize (H5 _ H4 oidx); simpl in H5; dest.

            (* discharge [RsEPred] *)
            red in H34.
            specialize (H34 eq_refl H30 (or_intror H29)).

            disc_InvExcl_this.
            { (* [InvObjExcl0] *)
              red; intros; split.
              { admit. }
              { disc_MsgConflictsInv oidx.
                eapply NoCohMsgs_rsDown_deq; eauto.
              }
            }
            { move H35 at bottom.

              red; simpl; intros.
              specialize (H35 H36).
              apply ObjsInvalid_this_state_silent.
              2: {
                intro Hx; elim Hx.
                apply rqEdgeUpFrom_subtreeIndsOf_self_in; auto.
                subst topo; congruence.
              }
              apply ObjsInvalid_this_deqMP_silent.
              2: {
                intro Hx; elim Hx.
                apply rqEdgeUpFrom_subtreeIndsOf_self_in; auto.
                subst topo; congruence.
              }
              assumption.
            }
          }
          { disc_InvExcl_others.
            { (* solve_by_ObjsInvalid_false oidx. *)
              disc_InvObjExcl0.
              disc_MsgConflictsInv oidx.
              exfalso.
              eapply ObjsInvalid_rsE_false with (oidx:= oidx); eauto.
              apply FirstMP_InMP; assumption.
            }
            { case_InvObjOwned.
              { (* solve_by_ObjsInvalid_false oidx. *)
                disc_MsgConflictsInv oidx.
                exfalso.
                eapply ObjsInvalid_rsE_false with (oidx:= oidx); eauto.
                apply FirstMP_InMP; assumption.
              }
              { disc_ObjsInvalid oidx0.
                case_ObjInvalid.
                { solve_ObjInvalid0. }
                { solve_ObjInvRs.
                  inv H38.
                  apply deqMP_InMP_midx; [|solve_chn_not_in].
                  assumption.
                }
              }
            }
          }
        }
      }

      { (* [l1DownSImm] *)
        disc_rule_conds_ex.

        assert (NoRsI oidx msgs).
        { solve_NoRsI_base.
          solve_NoRsI_by_rqDown oidx.
        }
        
        split.
        { msg_pred_admit. }
        { case_InvExcl_me_others.
          { disc_InvExcl_this.
            { solve_InvObjExcl0_by_ObjExcl0_false. }
            { solve_InvObjOwned_by_false. }
          }
          { disc_InvExcl_others.
            { disc_InvObjExcl0.
              solve_by_ObjsInvalid_false oidx.
            }
            { case_InvObjOwned.
              { solve_by_ObjsInvalid_false oidx. }
              { disc_ObjsInvalid oidx0.
                case_ObjInvalid.
                { solve_ObjInvalid0. }
                { solve_ObjInvRs.
                  inv H30.
                  apply InMP_or_enqMP; right.
                  apply deqMP_InMP_midx; [|solve_chn_not_in].
                  assumption.
                }
              }
            }
          }
        }
      }

      { (* [l1GetMImmE] *)
        disc_rule_conds_ex.
        exfalso; disc_AtomicMsgOutsInv (l1ExtOf oidx); eauto.
      }

      { (* [l1GetMImmM] *)
        disc_rule_conds_ex.
        exfalso; disc_AtomicMsgOutsInv (l1ExtOf oidx); eauto.
      }

      { (* [l1GetMRqUpUp] *)
        disc_rule_conds_ex.
        exfalso; disc_AtomicMsgOutsInv (l1ExtOf oidx); eauto.
      }
        
      { (* [l1GetMRsDownDown] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.

        assert (NoRsI oidx msgs).
        { solve_NoRsI_base.
          solve_NoRsI_by_rsDown oidx.
        }

        split.
        { msg_pred_admit. }
        { (** TODO: from [solve_InvExcl_trivial] *)
          match goal with
          | [He: InvExcl _ {| bst_orqs := ?orqs |}
             |- InvExcl _ {| bst_msgs := enqMP ?midx ?msg _ |}] =>
            eapply InvExcl_enq_sound
              with (porqs:= orqs) (nmsgs:= [(midx, msg)])
          end.
          2: {
            constructor; [|constructor].
            simpl; tauto.
          }

          case_InvExcl_me_others.
          { (* discharge [AtomicMsgOutsInv] *)
            move H5 at bottom.
            red in H5.
            rewrite Forall_forall in H5; specialize (H5 _ H4 oidx); simpl in H5; dest.

            (* discharge [RsEPred] *)
            red in H34.
            specialize (H34 eq_refl H30 (or_introl H29)).

            disc_InvExcl_this.
            { (* [InvObjExcl0] *)
              red; intros; split.
              { admit. }
              { disc_MsgConflictsInv oidx.
                eapply NoCohMsgs_rsDown_deq; eauto.
              }
            }
            { red; simpl; intros.
              apply ObjsInvalid_this_state_silent.
              2: {
                intro Hx; elim Hx.
                apply rqEdgeUpFrom_subtreeIndsOf_self_in; auto.
                subst topo; congruence.
              }
              apply ObjsInvalid_this_deqMP_silent.
              2: {
                intro Hx; elim Hx.
                apply rqEdgeUpFrom_subtreeIndsOf_self_in; auto.
                subst topo; congruence.
              }
              assumption.
            }
          }
          { admit. }
        }
      }

      { (* [l1DownIImm] *)
        disc_rule_conds_ex.

        assert (NoRsI oidx msgs).
        { solve_NoRsI_base.
          solve_NoRsI_by_rqDown oidx.
        }
        
        split.
        { msg_pred_admit. }
        { case_InvExcl_me_others.
          { disc_InvExcl_this.
            { solve_InvObjExcl0_by_ObjExcl0_false. }
            { solve_InvObjOwned_by_false. }
          }
          { disc_InvExcl_others.
            { disc_InvObjExcl0.
              solve_by_ObjsInvalid_false oidx.
            }
            { case_InvObjOwned.
              { solve_by_ObjsInvalid_false oidx. }
              { disc_ObjsInvalid oidx0.
                case_ObjInvalid.
                { solve_ObjInvalid0. }
                { solve_ObjInvRs.
                  inv H30.
                  apply InMP_or_enqMP; right.
                  apply deqMP_InMP_midx; [|solve_chn_not_in].
                  assumption.
                }
              }
            }
          }
        }
      }

      { (* [l1InvRqUpUp] *)
        disc_rule_conds_ex.
        exfalso; destruct rins; [auto|discriminate].
      }
      
      { (* [l1InvRqUpUpWB] *)
        disc_rule_conds_ex.
        exfalso; destruct rins; [auto|discriminate].
      }
      
      { (* [l1InvRsDownDown] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.

        split.
        { msg_pred_admit. }
        { case_InvExcl_me_others.
          { disc_InvExcl_this.
            { solve_InvObjExcl0_by_ObjExcl0_false. }
            { solve_InvObjOwned_by_false. }
          }
          { disc_InvExcl_others.
            { disc_InvObjExcl0; split.
              { move H6 at bottom.
                red; intros; specialize (H6 _ H33); mred; simpl in *.
                { left; split; simpl.
                  { solve_mesi. }
                  { disc_MsgConflictsInv oidx.
                    eapply NoCohMsgs_rsDown_deq; eauto.
                  }
                }
                { disc_bind_true.
                  case_ObjInvalid.
                  { solve_ObjInvalid0. }
                  { solve_ObjInvRs.
                    inv H35.
                    apply deqMP_InMP_midx; [|solve_chn_not_in].
                    assumption.
                  }
                }
              }
              { solve_MsgsP. }
            }
            { case_InvObjOwned.
              { left.
                red; simpl; split; [solve_mesi|].
                disc_MsgConflictsInv oidx.
                eapply NoCohMsgs_rsDown_deq; eauto.
              }
              { disc_ObjsInvalid oidx0.
                case_ObjInvalid.
                { solve_ObjInvalid0. }
                { solve_ObjInvRs.
                  inv H34.
                  apply deqMP_InMP_midx; [|solve_chn_not_in].
                  assumption.
                }
              }
            }
          }
        }
      }

  Qed.

  Lemma mesi_InvExcl_step:
    InvStep impl step_m (InvExcl topo).
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
    Invariant.InvReachable impl step_m (InvExcl topo).
  Proof.
    apply inv_reachable.
    - apply mesi_InvExcl_init.
    - apply mesi_InvExcl_step.
  Qed.

End InvExcl.

