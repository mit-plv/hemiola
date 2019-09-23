Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Require Export Ex.Mesi.MesiInvB.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Mesi.ImplOStateIfc.

Section CoherenceUnit.
  Variables (oidx: IdxT)
            (orq: ORq Msg)
            (ost: OState)
            (msgs: MessagePool Msg).

  Definition NoRsI :=
    MsgsNotExist [(downTo oidx, (MRs, mesiInvRs))] msgs.

  Definition NoRqI :=
    MsgsNotExist [(rqUpFrom oidx, (MRq, mesiInvWRq));
                    (rqUpFrom oidx, (MRq, mesiPushWRq))] msgs.

  (** 0) Coherence: which values are in a coherent state *)

  Definition ImplOStateMESI (cv: nat): Prop :=
    mesiS <= ost#[status] -> NoRsI -> ost#[val] = cv.

  Definition ObjOwned :=
    mesiS <= ost#[status] /\ ost#[owned] = true.

  Definition CohInvRq :=
    ObjOwned ->
    forall idm,
      InMPI msgs idm ->
      sigOf idm = (rqUpFrom oidx, (MRq, mesiInvWRq)) ->
      msg_value (valOf idm) = ost#[val].

  Definition CohPushRq :=
    ObjOwned ->
    forall idm,
      InMPI msgs idm ->
      sigOf idm = (rqUpFrom oidx, (MRq, mesiPushWRq)) ->
      msg_value (valOf idm) = ost#[val].

  (** 1) Exclusiveness: if a coherence unit is exclusive, then all other units
   * are in an invalid status. *)
  
  Definition ObjExcl0 :=
    mesiE <= ost#[status] /\ NoRsI.

  Definition ObjExcl :=
    ObjExcl0 \/
    MsgExistsSig (downTo oidx, (MRs, mesiRsE)) msgs \/
    MsgExistsSig (downTo oidx, (MRs, mesiRsM)) msgs.

  Definition NoCohMsgs :=
    MsgsNotExist [(downTo oidx, (MRs, mesiRsS));
                    (downTo oidx, (MRs, mesiRsE));
                    (rsUpFrom oidx, (MRs, mesiDownRsS))] msgs.

  Definition ObjInvalid0 :=
    ost#[status] = mesiI /\ NoCohMsgs.

  Definition ObjInvalid :=
    ObjInvalid0 \/
    MsgExistsSig (downTo oidx, (MRs, mesiInvRs)) msgs.

  (** 2) Clean "E" in MESI *)

  Definition ObjClean :=
    mesiS <= ost#[status] <= mesiE.

  Definition ObjDirME (cidx: IdxT) :=
    mesiE <= ost#[dir].(dir_st) /\ ost#[dir].(dir_excl) = cidx /\
    orq@[downRq] = None.

  Definition ObjDirE (cidx: IdxT) :=
    ost#[dir].(dir_st) = mesiE /\ ost#[dir].(dir_excl) = cidx /\
    orq@[downRq] = None.
  
  Definition ObjInvRq :=
    MsgExistsSig (rqUpFrom oidx, (MRq, mesiInvRq)) msgs.

  Definition ObjRqWB :=
    MsgExistsSig (rqUpFrom oidx, (MRq, mesiInvWRq)) msgs \/
    MsgExistsSig (rqUpFrom oidx, (MRq, mesiPushWRq)) msgs.

  Section Facts.

    Lemma NoRsI_MsgExistsSig_InvRs_false:
      MsgExistsSig (downTo oidx, (MRs, mesiInvRs)) msgs ->
      NoRsI -> False.
    Proof.
      intros.
      destruct H as [idm [? ?]].
      specialize (H0 _ H).
      unfold MsgP in H0.
      rewrite H1 in H0.
      unfold map, caseDec in H0.
      find_if_inside; auto.
    Qed.

  End Facts.

End CoherenceUnit.

Definition InvObjExcl0 (oidx: IdxT) (ost: OState) (msgs: MessagePool Msg) :=
  ObjExcl0 oidx ost msgs -> NoCohMsgs oidx msgs.

Definition InvExcl (st: MState): Prop :=
  forall eidx,
    eost <+- (bst_oss st)@[eidx];
      (InvObjExcl0 eidx eost (bst_msgs st) /\
       (ObjExcl eidx eost (bst_msgs st) ->
        forall oidx,
          oidx <> eidx ->
          ost <+- (bst_oss st)@[oidx];
            ObjInvalid oidx ost (bst_msgs st))).

Definition InvWB (st: MState): Prop :=
  forall oidx,
    ost <+- (bst_oss st)@[oidx];
      (CohInvRq oidx ost (bst_msgs st) /\
       CohPushRq oidx ost (bst_msgs st)).

Definition InvWBChild (topo: DTree) (st: MState): Prop :=
  forall oidx pidx,
    parentIdxOf topo oidx = Some pidx ->
    ost <+- (bst_oss st)@[oidx];
      post <+- (bst_oss st)@[pidx];
      porq <+- (bst_orqs st)@[pidx];
      (ObjDirME porq post oidx ->
       ObjRqWB oidx (bst_msgs st) ->
       ObjOwned ost).

Definition InvNonWB (topo: DTree) (st: MState): Prop :=
  forall oidx pidx,
    parentIdxOf topo oidx = Some pidx ->
    ost <+- (bst_oss st)@[oidx];
      post <+- (bst_oss st)@[pidx];
      porq <+- (bst_orqs st)@[pidx];
      (ObjDirE porq post oidx ->
       ObjInvRq oidx (bst_msgs st) ->
       (ObjClean ost /\ ost#[val] = post#[val])).

Definition InvForSim (topo: DTree) (st: MState): Prop :=
  InvExcl st /\
  InvWB st /\ InvWBChild topo st /\ InvNonWB topo st /\
  MesiDownLockInv topo st.

Section Facts.

  Lemma RootChnInv_root_NoRsI:
    forall tr bidx st,
      RootChnInv tr bidx st ->
      NoRsI (rootOf (fst (tree2Topo tr bidx))) (bst_msgs st).
  Proof.
    intros.
    do 3 red; intros.
    red; unfold map, fst, snd, caseDec.
    find_if_inside; auto.
    eapply H; [|eassumption].
    inv e; auto.
  Qed.
    
  Lemma RootChnInv_root_NoRqI:
    forall tr bidx st,
      RootChnInv tr bidx st ->
      NoRqI (rootOf (fst (tree2Topo tr bidx))) (bst_msgs st).
  Proof.
    intros.
    do 3 red; intros.
    red; unfold map, fst, snd, caseDec.
    do 2 (find_if_inside; [eapply H; [|eassumption]; inv e; auto|]).
    auto.
  Qed.

  Lemma InvExcl_excl_invalid:
    forall st (He: InvExcl st) msgs eidx eost,
      bst_msgs st = msgs ->
      (bst_oss st)@[eidx] = Some eost ->
      NoRsI eidx msgs ->
      mesiE <= eost#[status] ->
      forall oidx ost,
        oidx <> eidx ->
        (bst_oss st)@[oidx] = Some ost ->
        ObjInvalid oidx ost msgs.
  Proof.
    intros; subst.
    specialize (He eidx).
    disc_rule_conds_ex.
    unfold ObjExcl, ObjExcl0 in H5; simpl in H5.
    specialize (H5 (or_introl (conj H2 H1)) _ H3).
    solve_rule_conds_ex.
  Qed.

  Corollary InvExcl_excl_invalid_status:
    forall st (He: InvExcl st) eidx eost,
      (bst_oss st)@[eidx] = Some eost ->
      NoRsI eidx (bst_msgs st) ->
      mesiE <= eost#[status] ->
      forall oidx ost,
        oidx <> eidx ->
        (bst_oss st)@[oidx] = Some ost ->
        NoRsI oidx (bst_msgs st) ->
        ost#[status] = mesiI.
  Proof.
    intros.
    eapply InvExcl_excl_invalid in H1; eauto.
    destruct H1.
    - apply H1.
    - exfalso; eapply NoRsI_MsgExistsSig_InvRs_false; eauto.
  Qed.
  
End Facts.

Section InvWB.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma mesi_InvWB_init:
    Invariant.InvInit impl InvWB.
  Proof.
    do 2 (red; simpl).
    intros.
    destruct (implOStatesInit tr)@[oidx] as [orq|] eqn:Host; simpl; auto.
    destruct (in_dec idx_dec oidx (c_li_indices cifc ++ c_l1_indices cifc)).
    - subst cifc; rewrite c_li_indices_head_rootOf in i by assumption.
      inv i.
      + rewrite implOStatesInit_value_root in Host by assumption.
        inv Host; split.
        all: red; intros; do 2 (red in H0); dest_in.
      + rewrite implOStatesInit_value_non_root in Host by assumption.
        inv Host; split.
        all: red; intros; red in H0; simpl in H0; dest; discriminate.
    - rewrite implOStatesInit_None in Host by assumption.
      discriminate.
  Qed.

  Lemma mesi_InvWB_ext_in:
    forall oss orqs msgs,
      InvWB {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        InvWB {| bst_oss := oss; bst_orqs := orqs; bst_msgs := enqMsgs eins msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H oidx); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    dest; split.
    - red; intros.
      apply InMP_enqMsgs_or in H4.
      destruct H4; [|eapply H; eauto].
      apply in_map with (f:= idOf) in H4; simpl in H4.
      apply H1 in H4; simpl in H4.
      exfalso; eapply DisjList_In_1.
      + apply tree2Topo_minds_merqs_disj.
      + eassumption.
      + eapply tree2Topo_obj_chns_minds_SubList.
        * specialize (H0 oidx); simpl in H0.
          rewrite Host in H0; simpl in H0.
          eassumption.
        * destruct idm as [midx msg]; inv H5.
          simpl; tauto.

    - red; intros.
      apply InMP_enqMsgs_or in H4.
      destruct H4; [|eapply H2; eauto].
      apply in_map with (f:= idOf) in H4; simpl in H4.
      apply H1 in H4; simpl in H4.
      exfalso; eapply DisjList_In_1.
      + apply tree2Topo_minds_merqs_disj.
      + eassumption.
      + eapply tree2Topo_obj_chns_minds_SubList.
        * specialize (H0 oidx); simpl in H0.
          rewrite Host in H0; simpl in H0.
          eassumption.
        * destruct idm as [midx msg]; inv H5.
          simpl; tauto.
  Qed.

  Lemma mesi_InvWB_ext_out:
    forall oss orqs msgs,
      InvWB {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall (eouts: list (Id Msg)),
        InvWB {| bst_oss := oss;
                 bst_orqs := orqs;
                 bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H oidx); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    dest; split.
    all: red; intros; apply InMP_deqMsgs in H3; auto.
  Qed.

  Lemma InvWB_no_update:
    forall oss orqs msgs,
      InvWB {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall oidx (post nost: OState),
        oss@[oidx] = Some post ->
        nost#[val] = post#[val] ->
        nost#[owned] = post#[owned] ->
        nost#[status] = post#[status] ->
        InvWB {| bst_oss:= oss +[oidx <- nost];
                 bst_orqs:= orqs; bst_msgs:= msgs |}.
  Proof.
    unfold InvWB; simpl; intros.
    mred; simpl; auto.
    specialize (H oidx).
    rewrite H0 in H; simpl in H.
    dest; split.
    - red; intros.
      simpl; rewrite H1.
      apply H; auto.
      red; simpl; rewrite <-H2, <-H3.
      assumption.
    - red; intros.
      simpl; rewrite H1.
      apply H4; auto.
      red; simpl; rewrite <-H2, <-H3.
      assumption.
  Qed.

  Lemma InvWB_update_owned_false:
    forall oss orqs msgs,
      InvWB {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall oidx (ost: OState),
        ost#[owned] = false ->
        InvWB {| bst_oss:= oss +[oidx <- ost];
                 bst_orqs:= orqs; bst_msgs:= msgs |}.
  Proof.
    unfold InvWB; simpl; intros.
    mred; simpl; auto.
    split; red; intros.
    all: destruct H1; simpl in *; congruence.
  Qed.

  Lemma InvWB_update_status_invalid:
    forall oss orqs msgs,
      InvWB {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall oidx (ost: OState),
        ost#[status] < mesiS ->
        InvWB {| bst_oss:= oss +[oidx <- ost];
                 bst_orqs:= orqs; bst_msgs:= msgs |}.
  Proof.
    unfold InvWB; simpl; intros.
    mred; simpl; auto.
    split; red; intros.
    all: destruct H1; simpl in *; solve_mesi.
  Qed.

  Lemma InvWB_other_msg_id_enqMP:
    forall oss orqs msgs,
      InvWB {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx msg,
        msg.(msg_id) <> mesiInvWRq ->
        msg.(msg_id) <> mesiPushWRq ->
        InvWB {| bst_oss:= oss; bst_orqs:= orqs;
                 bst_msgs:= enqMP midx msg msgs |}.
  Proof.
    unfold InvWB; simpl; intros.
    specialize (H oidx).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    dest; split.
    - red; intros.
      apply InMP_enqMP_or in H4; destruct H4; auto.
      dest; subst.
      destruct idm as [midx msg]; simpl in *.
      inv H5; exfalso; auto.
    - red; intros.
      apply InMP_enqMP_or in H4; destruct H4; auto.
      dest; subst.
      destruct idm as [midx msg]; simpl in *.
      inv H5; exfalso; auto.
  Qed.
  
  Lemma InvWB_other_msg_id_enqMsgs:
    forall oss orqs msgs,
      InvWB {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall nmsgs,
        Forall (fun idm =>
                  (valOf idm).(msg_id) <> mesiInvWRq /\
                  (valOf idm).(msg_id) <> mesiPushWRq) nmsgs ->
        InvWB {| bst_oss:= oss; bst_orqs:= orqs;
                 bst_msgs:= enqMsgs nmsgs msgs |}.
  Proof.
    intros.
    generalize dependent msgs.
    induction nmsgs as [|[nmidx nmsg] nmsgs]; simpl; intros; auto.
    inv H0; dest.
    apply IHnmsgs; auto.
    apply InvWB_other_msg_id_enqMP; assumption.
  Qed.

  Lemma InvWB_deqMP:
    forall oss orqs msgs,
      InvWB {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx,
        InvWB {| bst_oss:= oss; bst_orqs:= orqs;
                 bst_msgs:= deqMP midx msgs |}.
  Proof.
    unfold InvWB; simpl; intros.
    specialize (H oidx).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    dest; split.
    all: red; intros; apply InMP_deqMP in H2; auto.
  Qed.

  Lemma InvWB_deqMsgs:
    forall oss orqs msgs,
      InvWB {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall minds,
        InvWB {| bst_oss:= oss; bst_orqs:= orqs;
                 bst_msgs:= deqMsgs minds msgs |}.
  Proof.
    unfold InvWB; simpl; intros.
    specialize (H oidx).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    dest; split.
    all: red; intros; apply InMP_deqMsgs in H2; auto.
  Qed.

  Lemma mesi_InvWB_step:
    Invariant.InvStep impl step_m InvWB.
  Proof.
    red; intros.
    pose proof (mesi_InObjInds H) as Hioi.
    (* pose proof (tree2Topo_TreeTopoNode tr 0) as Htn. *)
    (* pose proof (footprints_ok *)
    (*               (mesi_GoodORqsInit Htr) *)
    (*               (mesi_GoodRqRsSys Htr) H) as Hftinv. *)
    (* pose proof (mesi_footprints_ok H) as Hmftinv. *)
    inv H1; [assumption
            |apply mesi_InvWB_ext_in; auto
            |apply mesi_InvWB_ext_out; auto
            |].

    simpl in H2; destruct H2; [subst|apply in_app_or in H1; destruct H1].

    - (*! Cases for the main memory *)

      (** Abstract the root. *)
      remember (rootOf (fst (tree2Topo tr 0))) as oidx; clear Heqoidx.

      (** Do case analysis per a rule. *)
      apply in_app_or in H3; destruct H3.

      1: { (** Rules per a child *)
        apply concat_In in H1; destruct H1 as [crls [? ?]].
        apply in_map_iff in H1; destruct H1 as [cidx [? ?]]; subst.
        dest_in.

        { disc_rule_conds_ex.

          Ltac solve_InvWB_enqMP :=
            simpl;
            try match goal with
                | [H: msg_id ?rmsg = _ |- msg_id ?rmsg <> _] => rewrite H
                end;
            discriminate.

          Ltac solve_InvWB_enqMsgs :=
            let idm := fresh "idm" in
            let Hin := fresh "H" in
            apply Forall_forall; intros idm Hin;
            apply in_map_iff in Hin; dest; subst;
            split; solve_InvWB_enqMP.

          Ltac solve_InvWB :=
            repeat
              (first [apply InvWB_other_msg_id_enqMP; [|solve_InvWB_enqMP..]
                     |apply InvWB_other_msg_id_enqMsgs; [|solve_InvWB_enqMsgs]
                     |apply InvWB_deqMP
                     |apply InvWB_deqMsgs
                     |eapply InvWB_no_update; [|eauto; fail..]
                     |apply InvWB_update_owned_false; [|reflexivity]
                     |apply InvWB_update_status_invalid; [|simpl; solve_mesi]
                     |assumption]).

          solve_InvWB.
        }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB.
          admit. (** TODO: NoRqI by uplock-free *)
        }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB.
          admit. (** TODO: NoRqI by uplock-free *)
        }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB.
          admit. (** TODO: NoRqI by uplock-free *)
        }          

      }

      dest_in.
      { disc_rule_conds_ex; solve_InvWB. 
        admit. (** ??? *)
      }
      { disc_rule_conds_ex; solve_InvWB. }

    - (*! Cases for Li caches *)
      (* unfold InvWB in *; simpl in *. *)

      (** Derive some necessary information: each Li has a parent. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst; simpl in *.
      (* pose proof (c_li_indices_tail_has_parent Htr _ _ H2). *)
      (* destruct H1 as [pidx [? ?]]. *)
      (* pose proof (Htn _ _ H4); dest. *)
      
      (** Do case analysis per a rule. *)
      apply in_app_or in H3; destruct H3.

      1: { (** Rules per a child *)
        apply concat_In in H1; destruct H1 as [crls [? ?]].
        apply in_map_iff in H1; destruct H1 as [cidx [? ?]]; subst.
        dest_in.

        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB.
          admit. (** TODO: NoRqI by uplock-free *)
        }          
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB.
          admit. (** TODO: NoRqI by uplock-free *)
        }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB. }
        { disc_rule_conds_ex; solve_InvWB.
          admit. (** TODO: NoRqI by uplock-free *)
        }

      }

      dest_in.

      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB.
        admit. (** ??? *)
      }
      { disc_rule_conds_ex; solve_InvWB.
        admit. (** ??? *)
      }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB.
        admit. (** TODO: [InvWB], just emitted [mesiInvWRq] *)
      }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB.
        admit. (** TODO: [InvWB], just emitted [mesiPushWRq] *)
      }

    - (*! Cases for L1 caches *)

      (** Do case analysis per a rule. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst.
      dest_in.

      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB.
        admit. (** TODO: NoRqI by rsDown *)
      }
      { disc_rule_conds_ex; solve_InvWB.
        admit. (** TODO: NoRqI by rsDown *)
      }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB.
        admit. (** TODO: [InvWB] preserved when E -> M *)
      }
      { disc_rule_conds_ex; solve_InvWB.
        admit. (** TODO: NoRqI by uplock-free *)
      }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB.
        admit. (** TODO: NoRqI by rsDown *)
      }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB. }
      { disc_rule_conds_ex; solve_InvWB.
        admit. (** TODO: [InvWB], just emitted [mesiInvWRq] *)
      }
      { disc_rule_conds_ex; solve_InvWB. }
  Admitted.

  Theorem mesi_InvWB_ok:
    InvReachable impl step_m InvWB.
  Proof.
    apply inv_reachable.
    - apply mesi_InvWB_init.
    - apply mesi_InvWB_step.
  Qed.

End InvWB.

(** The invariants proof starts here -- *)

Lemma mesi_InvForSim_init:
  forall tr (Htr: tr <> Node nil),
    InvForSim (fst (tree2Topo tr 0)) (initsOf (impl Htr)).
Proof.
Admitted.

Lemma mesi_InvForSim_ok:
  forall tr (Htr: tr <> Node nil),
    InvStep (impl Htr) step_m (InvForSim (fst (tree2Topo tr 0))).
Proof.
Admitted.

Ltac solve_NoRsI_base :=
  repeat
    match goal with
    | |- NoRsI _ _ => do 3 red; intros
    | |- MsgP _ _ =>
      red; unfold map, caseDec, fst;
      repeat (find_if_inside; [simpl|auto])
    | [H: sigOf ?idm = _ |- _] =>
      let midx := fresh "midx" in
      let msg := fresh "msg" in
      destruct idm as [midx msg]; inv H
    end.

Ltac solve_NoRsI_by_no_locks oidx :=
  repeat
    match goal with
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (c_l1_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (tl (c_li_indices _)),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_introl (tl_In _ _ Hin))) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcf: RsDownConflicts oidx _ ?msgs,
             Hinm: InMPI ?msgs (?midx, ?msg),
                   Hmt: msg_type ?msg = MRs |- _] =>
      specialize (Hmcf (midx, msg) eq_refl
                       ltac:(simpl; rewrite Hmt; reflexivity)
                              Hinm); dest; auto
    end.

Ltac solve_NoRsI_by_rqUp oidx :=
  repeat
    match goal with
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (c_li_indices _ ++ c_l1_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ Hin Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcf: RsDownConflicts oidx _ ?msgs,
             Hinm: InMPI ?msgs (?rsd, ?msg),
                   Hmt: msg_type ?msg = MRs,
                        Hfmp: FirstMPI ?msgs (?rqu, ?rmsg) |- _] =>
      specialize (Hmcf (rsd, msg) eq_refl
                       ltac:(simpl; rewrite Hmt; reflexivity)
                              Hinm);
      let Hrqu := fresh "H" in
      destruct Hmcf as [_ [Hrqu _]];
      apply Hrqu with (rqUp:= (rqu, rmsg)); auto
    | |- InMPI _ _ => red; solve_in_mp
    end.

Ltac solve_NoRsI_by_rqDown oidx :=
  repeat
    match goal with
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (c_l1_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (tl (c_li_indices _)),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_introl (tl_In _ _ Hin))) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcf: RsDownConflicts oidx _ ?msgs,
             Hinm: InMPI ?msgs (?midx, ?msg),
                   Hmt: msg_type ?msg = MRs |- _] =>
      specialize (Hmcf (midx, msg) eq_refl
                       ltac:(simpl; rewrite Hmt; reflexivity)
                              Hinm);
      let Hrqd := fresh "H" in
      destruct Hmcf as [_ [_ [_ [Hrqd _]]]];
      eapply Hrqd; try eassumption; try reflexivity; assumption
    end.

Ltac solve_NoRsI_by_rsDown oidx :=
  repeat
    match goal with
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (c_l1_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcf: RsDownConflicts oidx _ ?msgs,
             Hinm: InMPI ?msgs (?midx, ?msg),
                   Hmt: msg_type ?msg = MRs,
                        Hfmp: FirstMPI ?msgs (?midx, ?rmsg) |- _] =>
      specialize (Hmcf (midx, msg) eq_refl
                       ltac:(simpl; rewrite Hmt; reflexivity)
                              Hinm);
      let Hrqd := fresh "H" in
      destruct Hmcf as [_ [_ [Hrqd _]]];
      eapply Hrqd with (rrsDown:= (midx, rmsg));
      try eassumption; try reflexivity
    | |- valOf (_, ?msg1) <> valOf (_, ?msg2) =>
      let Hx := fresh "H" in
      destruct msg1, msg2; simpl in *; intro Hx; inv Hx; discriminate
    | |- InMPI _ _ => red; solve_in_mp
    end.

Ltac solve_NoRqI_base :=
  repeat
    match goal with
    | |- NoRqI _ _ => do 3 red; intros
    | |- MsgP _ _ =>
      red; unfold map, caseDec, fst;
      repeat (find_if_inside; [simpl|auto])
    | [H: sigOf ?idm = _ |- _] =>
      let midx := fresh "midx" in
      let msg := fresh "msg" in
      destruct idm as [midx msg]; inv H
    end.

Ltac solve_NoRqI_by_no_locks oidx :=
  repeat
    match goal with
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (c_l1_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (tl (c_li_indices _)),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_introl (tl_In _ _ Hin))) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcf: RqUpConflicts oidx _ ?msgs, Hinm: InMPI ?msgs (?midx, ?msg) |- _] =>
      specialize (Hmcf (midx, msg) eq_refl Hinm); dest; auto
    end.

Ltac solve_NoRqI_by_rsDown oidx :=
  repeat
    match goal with
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (c_l1_indices _),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_intror Hin)) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcfi: MsgConflictsInv _ _ {| bst_orqs:= ?orqs |},
              Hin: In oidx (tl (c_li_indices _)),
                   Horq: ?orqs@[oidx] = Some _ |- _] =>
      specialize (Hmcfi oidx _ (in_or_app _ _ _ (or_introl (tl_In _ _ Hin))) Horq);
      simpl in Hmcfi; destruct Hmcfi
    | [Hmcf: RsDownConflicts oidx _ ?msgs,
             Hfmp: FirstMPI ?msgs (?down, ?msg),
                   Hmt: msg_type ?msg = MRs,
                        Hinm: InMPI ?msgs (?rqu, ?rmsg) |- _] =>
      apply FirstMP_InMP in Hfmp;
      specialize (Hmcf (down, msg) eq_refl
                       ltac:(simpl; rewrite Hmt; reflexivity)
                              Hfmp);
      let Hrqu := fresh "H" in
      destruct Hmcf as [_ [Hrqu _]];
      eapply Hrqu with (rqUp:= (rqu, rmsg));
      try eassumption; try reflexivity
    end.

Ltac derive_ObjDirE oidx cidx :=
  match goal with
  | [Host: ?oss@[oidx] = Some ?ost,
           Horq: ?orqs@[oidx] = Some ?orq |- _] =>
    assert (ObjDirE orq ost cidx) by (repeat split; assumption)
  end.

Ltac derive_ObjDirME oidx cidx :=
  match goal with
  | [Host: ?oss@[oidx] = Some ?ost,
           Horq: ?orqs@[oidx] = Some ?orq |- _] =>
    assert (ObjDirME orq ost cidx) by (repeat split; assumption)
  end.

Ltac derive_ObjInvRq oidx :=
  match goal with
  | [H: FirstMPI ?msgs (rqUpFrom oidx, ?rmsg) |- _] =>
    assert (ObjInvRq oidx msgs)
      by (exists (rqUpFrom oidx, rmsg); split;
                 [red; simpl; solve_in_mp|unfold sigOf; simpl; congruence])
  end.

Ltac derive_ObjRqWB_inv oidx :=
  match goal with
  | [H: FirstMPI ?msgs (rqUpFrom oidx, ?rmsg) |- _] =>
    assert (ObjRqWB oidx msgs)
      by (left; eexists; split;
          [eapply FirstMP_InMP; eassumption
          |unfold sigOf; simpl; congruence])
  end.

Ltac derive_ObjRqWB_push oidx :=
  match goal with
  | [H: FirstMPI ?msgs (rqUpFrom oidx, ?rmsg) |- _] =>
    assert (ObjRqWB oidx msgs)
      by (right; eexists; split;
          [eapply FirstMP_InMP; eassumption
          |unfold sigOf; simpl; congruence])
  end.

Ltac disc_InvNonWB cidx Hinv :=
  repeat
    match goal with
    | [Hp: parentIdxOf _ cidx = Some _ |- _] =>
      specialize (Hinv _ _ Hp); simpl in Hinv;
      disc_rule_conds_ex
    end.

Ltac disc_InvWB_inv cidx Hinv :=
  specialize (Hinv cidx); simpl in Hinv;
  disc_rule_conds_ex;
  match goal with
  | [Hcoh: CohInvRq cidx ?ost _, Ho: ObjOwned ?ost, Hfm: FirstMPI _ _ |- _] =>
    specialize (Hcoh Ho _ (FirstMP_InMP Hfm));
    unfold sigOf in Hcoh; simpl in Hcoh;
    specialize (Hcoh ltac:(congruence))
  end.

Ltac disc_InvWB_push cidx Hinv :=
  specialize (Hinv cidx); simpl in Hinv;
  disc_rule_conds_ex;
  match goal with
  | [Hcoh: CohPushRq cidx ?ost _, Ho: ObjOwned ?ost, Hfm: FirstMPI _ _ |- _] =>
    specialize (Hcoh Ho _ (FirstMP_InMP Hfm));
    unfold sigOf in Hcoh; simpl in Hcoh;
    specialize (Hcoh ltac:(congruence))
  end.

Ltac disc_InvWBChild cidx Hinv :=
  match goal with
  | [Hp: parentIdxOf _ cidx = Some _ |- _] =>
    specialize (Hinv _ _ Hp); simpl in Hinv;
    disc_rule_conds_ex
  end.

Hint Unfold NoRsI ImplOStateMESI: RuleConds.
Hint Unfold InvForSim: RuleConds.

