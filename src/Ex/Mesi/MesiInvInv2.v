Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsInvMsg RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Require Import Ex.Mesi.MesiInv Ex.Mesi.MesiInvInv0 Ex.Mesi.MesiInvInv1.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Mesi.ImplOStateIfc.

Definition ObjInvNotOwned (oidx: IdxT) (ost: OState) (msgs: MessagePool Msg) :=
  ObjInvRq oidx msgs -> ost#[owned] = false.

Definition InvNotOwned (st: State): Prop :=
  forall oidx,
    ost <+- (st_oss st)@[oidx]; ObjInvNotOwned oidx ost (st_msgs st).

Section InvNotOwned.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma mesi_InvNotOwned_init:
    Invariant.InvInit impl InvNotOwned.
  Proof.
    do 2 (red; simpl).
    intros.
    destruct (implOStatesInit tr)@[oidx] as [orq|] eqn:Host; simpl; auto.
    red; intros.
    destruct H as [idm [? ?]].
    do 2 red in H; dest_in.
  Qed.

  Lemma mesi_InvNotOwned_ext_in:
    forall oss orqs msgs,
      InvNotOwned {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      InObjInds tr 0 {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        InvNotOwned {| st_oss := oss; st_orqs := orqs; st_msgs := enqMsgs eins msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H oidx); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    red; intros.
    destruct H2 as [idm [? ?]].
    apply InMP_enqMsgs_or in H2.
    destruct H2; [|apply H; do 2 red; eauto].
    apply in_map with (f:= idOf) in H2; simpl in H2.
    apply H1 in H2; simpl in H2.
    exfalso; eapply DisjList_In_1.
    - apply tree2Topo_minds_merqs_disj.
    - eassumption.
    - eapply tree2Topo_obj_chns_minds_SubList.
      + specialize (H0 oidx); simpl in H0.
        rewrite Host in H0; simpl in H0.
        eassumption.
      + destruct idm as [midx msg]; inv H3.
        simpl; tauto.
  Qed.

  Lemma mesi_InvNotOwned_ext_out:
    forall oss orqs msgs,
      InvNotOwned {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      InObjInds tr 0 {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      forall (eouts: list (Id Msg)),
        InvNotOwned {| st_oss := oss;
                       st_orqs := orqs;
                       st_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H oidx); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    red; intros.
    destruct H1 as [idm [? ?]].
    apply InMP_deqMsgs in H1.
    apply H; do 2 red; eauto.
  Qed.

  Lemma InvNotOwned_no_update:
    forall oss orqs msgs,
      InvNotOwned {| st_oss:= oss; st_orqs:= orqs; st_msgs:= msgs |} ->
      forall oidx (post nost: OState),
        oss@[oidx] = Some post ->
        nost#[owned] = post#[owned] ->
        InvNotOwned {| st_oss:= oss +[oidx <- nost];
                       st_orqs:= orqs; st_msgs:= msgs |}.
  Proof.
    unfold InvNotOwned; simpl; intros.
    mred; simpl; auto.
    specialize (H oidx).
    rewrite H0 in H; simpl in H.
    red; intros.
    simpl; rewrite H1; auto.
  Qed.

  Lemma InvNotOwned_update_status_NoRqI_NoRsI:
    forall oss orqs msgs,
      InvNotOwned {| st_oss:= oss; st_orqs:= orqs; st_msgs:= msgs |} ->
      forall oidx (ost: OState),
        NoRqI oidx msgs ->
        InvNotOwned {| st_oss:= oss +[oidx <- ost];
                       st_orqs:= orqs; st_msgs:= msgs |}.
  Proof.
    unfold InvNotOwned; simpl; intros.
    mred; simpl; auto.
    red; intros.
    exfalso.
    eapply MsgExistsSig_MsgsNotExist_false; [apply H0| |eassumption].
    simpl; tauto.
  Qed.

  Lemma InvNotOwned_enqMP_rq_valid:
    forall oss orqs msgs,
      InvNotOwned {| st_oss:= oss; st_orqs:= orqs; st_msgs:= msgs |} ->
      forall oidx ost midx msg,
        oss@[oidx] = Some ost ->
        ost#[owned] = false ->
        midx = rqUpFrom oidx ->
        msg.(msg_id) = mesiInvRq ->
        InvNotOwned {| st_oss:= oss; st_orqs:= orqs;
                       st_msgs:= enqMP midx msg msgs |}.
  Proof.
    unfold InvNotOwned; simpl; intros.
    destruct (idx_dec oidx0 oidx); subst.
    - specialize (H oidx).
      rewrite H0 in *; simpl in *.
      red; intros; auto.
    - specialize (H oidx0).
      destruct (oss@[oidx0]) as [ost0|]; simpl in *; auto.
      red; intros.
      destruct H2 as [idm [? ?]].
      apply InMP_enqMP_or in H2; destruct H2.
      + dest; inv H4; rewrite H2 in H7; inv H7.
        exfalso; auto.
      + apply H; do 2 red; eauto.
  Qed.

  Lemma InvNotOwned_other_msg_id_enqMP:
    forall oss orqs msgs,
      InvNotOwned {| st_oss:= oss; st_orqs:= orqs; st_msgs:= msgs |} ->
      forall midx msg,
        msg.(msg_id) <> mesiInvRq ->
        InvNotOwned {| st_oss:= oss; st_orqs:= orqs;
                       st_msgs:= enqMP midx msg msgs |}.
  Proof.
    unfold InvNotOwned; simpl; intros.
    specialize (H oidx).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    red; intros.
    destruct H1 as [idm [? ?]].
    apply InMP_enqMP_or in H1; destruct H1.
    - dest; subst; inv H2; exfalso; auto.
    - apply H; do 2 red; eauto.
  Qed.

  Lemma InvNotOwned_other_msg_id_enqMsgs:
    forall oss orqs msgs,
      InvNotOwned {| st_oss:= oss; st_orqs:= orqs; st_msgs:= msgs |} ->
      forall nmsgs,
        Forall (fun idm => (valOf idm).(msg_id) <> mesiInvWRq /\
                           (valOf idm).(msg_id) <> mesiInvRq /\
                           (valOf idm).(msg_id) <> mesiInvRs) nmsgs ->
        InvNotOwned {| st_oss:= oss; st_orqs:= orqs;
                       st_msgs:= enqMsgs nmsgs msgs |}.
  Proof.
    intros.
    generalize dependent msgs.
    induction nmsgs as [|[nmidx nmsg] nmsgs]; simpl; intros; auto.
    inv H0; dest.
    apply IHnmsgs; auto.
    apply InvNotOwned_other_msg_id_enqMP; assumption.
  Qed.

  Lemma InvNotOwned_deqMP:
    forall oss orqs msgs,
      InvNotOwned {| st_oss:= oss; st_orqs:= orqs; st_msgs:= msgs |} ->
      forall midx,
        InvNotOwned {| st_oss:= oss; st_orqs:= orqs;
                       st_msgs:= deqMP midx msgs |}.
  Proof.
    unfold InvNotOwned; simpl; intros.
    specialize (H oidx).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    red; intros.
    destruct H0 as [idm [? ?]].
    apply InMP_deqMP in H0.
    apply H; do 2 red; eauto.
  Qed.

  Lemma InvNotOwned_deqMsgs:
    forall oss orqs msgs,
      InvNotOwned {| st_oss:= oss; st_orqs:= orqs; st_msgs:= msgs |} ->
      forall minds,
        InvNotOwned {| st_oss:= oss; st_orqs:= orqs;
                       st_msgs:= deqMsgs minds msgs |}.
  Proof.
    unfold InvNotOwned; simpl; intros.
    specialize (H oidx).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    red; intros.
    destruct H0 as [idm [? ?]].
    apply InMP_deqMsgs in H0.
    apply H; do 2 red; eauto.
  Qed.

  Ltac simpl_InvNotOwned_enqMP :=
    simpl;
    try match goal with
        | [H: msg_id ?rmsg = _ |- msg_id ?rmsg <> _] => rewrite H
        end;
    discriminate.

  Ltac simpl_InvNotOwned_enqMsgs :=
    let idm := fresh "idm" in
    let Hin := fresh "H" in
    apply Forall_forall; intros idm Hin;
    apply in_map_iff in Hin; dest; subst;
    repeat ssplit; simpl_InvNotOwned_enqMP.

  Ltac simpl_InvNotOwned :=
    repeat
      (first [apply InvNotOwned_other_msg_id_enqMP; [|simpl_InvNotOwned_enqMP..]
             |apply InvNotOwned_other_msg_id_enqMsgs; [|simpl_InvNotOwned_enqMsgs]
             |apply InvNotOwned_deqMP
             |apply InvNotOwned_deqMsgs
             |apply InvNotOwned_update_status_NoRqI_NoRsI; [|assumption..]
             |eapply InvNotOwned_no_update; [|eauto; fail..]
             |assumption]).

  Ltac solve_InvNotOwned :=
    let oidx := fresh "oidx" in
    red; simpl; intros oidx;
    match goal with
    | [Hi: InvNotOwned _ |- _] =>
      specialize (Hi oidx); simpl in Hi;
      mred; simpl;
      let Hinv := fresh "H" in
      intros Hinv;
      specialize (Hi Hinv)
    end;
    simpl in *; try reflexivity; try solve_mesi.

  Lemma mesi_InvNotOwned_step:
    Invariant.InvStep impl step_m InvNotOwned.
  Proof. (* SKIP_PROOF_ON
    red; intros.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (mesi_InObjInds H) as Hioi.
    pose proof (mesi_MsgConflictsInv
                  (@mesi_RootChnInv_ok _ Htr) H) as Hpmcf.
    pose proof (MesiDownLockInv_ok H) as Hmdl.
    pose proof (mesi_InvWBDir_ok H) as Hwd.
    inv H1; [assumption
            |apply mesi_InvNotOwned_ext_in; auto
            |apply mesi_InvNotOwned_ext_out; auto
            |].

    simpl in H2; destruct H2; [subst|apply in_app_or in H1; destruct H1].

    - (*! Cases for the main memory *)

      (** Abstract the root. *)
      assert (In (rootOf (fst (tree2Topo tr 0)))
                 (c_li_indices (snd (tree2Topo tr 0)))) as Hin.
      { rewrite c_li_indices_head_rootOf by assumption.
        left; reflexivity.
      }

      remember (rootOf (fst (tree2Topo tr 0))) as oidx; clear Heqoidx.

      (** Do case analysis per a rule. *)
      apply in_app_or in H3; destruct H3.

      1: { (** Rules per a child *)
        apply concat_In in H1; destruct H1 as [crls [? ?]].
        apply in_map_iff in H1; destruct H1 as [cidx [? ?]]; subst.
        dest_in; disc_rule_conds_ex.

        all: try (simpl_InvNotOwned; fail).
        all: try (assert (NoRqI oidx msgs)
                   by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx);
                  simpl_InvNotOwned).
      }

      dest_in.
      { disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        simpl_InvNotOwned; solve_InvNotOwned.
        derive_InvWBDir oidx.
        specialize (Hwd (or_intror (or_introl H18))).
        simpl in Hwd; solve_mesi.
      }
      { disc_rule_conds_ex.
        simpl_InvNotOwned; solve_InvNotOwned.
      }
      { disc_rule_conds_ex.
        simpl_InvNotOwned; solve_InvNotOwned.
      }

    - (*! Cases for Li caches *)

      (** Derive some necessary information: each Li has a parent. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst; simpl in *.

      pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
      pose proof (c_li_indices_tail_has_parent Htr _ _ H2).
      destruct H1 as [pidx [? ?]].
      pose proof (Htn _ _ H4); dest.

      (** Do case analysis per a rule. *)
      apply in_app_or in H3; destruct H3.

      1: { (** Rules per a child *)
        apply concat_In in H3; destruct H3 as [crls [? ?]].
        apply in_map_iff in H3; destruct H3 as [cidx [? ?]]; subst.
        dest_in; disc_rule_conds_ex.

        all: try (simpl_InvNotOwned; fail).
        all: try (assert (NoRqI oidx msgs)
                   by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx);
                  simpl_InvNotOwned).
      }

      dest_in; disc_rule_conds_ex.

      all: try (simpl_InvNotOwned; fail).
      all: try (derive_footprint_info_basis oidx;
                assert (NoRqI oidx msgs)
                  by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx);
                simpl_InvNotOwned).
      all: try (simpl_InvNotOwned; solve_InvNotOwned; fail).
      { disc_MesiDownLockInv oidx Hmdl.
        simpl_InvNotOwned; solve_InvNotOwned.
        derive_InvWBDir oidx.
        specialize (Hwd (or_intror (or_introl H24))).
        simpl in Hwd; solve_mesi.
      }
      { eapply InvNotOwned_enqMP_rq_valid; eauto.
        { solve_InvNotOwned. }
        { mred. }
        { assumption. }
      }

    - (*! Cases for L1 caches *)

      (** Derive some necessary information: each Li has a parent. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst.

      pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
      pose proof (c_l1_indices_has_parent Htr _ _ H2).
      destruct H1 as [pidx [? ?]].
      pose proof (Htn _ _ H4); dest.

      (** Register an invariant that holds only for L1 caches. *)
      pose proof (mesi_InvL1DirI_ok H) as Hl1d.
      red in Hl1d; simpl in Hl1d.
      rewrite Forall_forall in Hl1d; specialize (Hl1d _ H2).
      simpl in H5; rewrite H5 in Hl1d; simpl in Hl1d.

      (** Do case analysis per a rule. *)
      dest_in; disc_rule_conds_ex.

      all: try (simpl_InvNotOwned; fail).
      all: try (simpl_InvNotOwned; solve_InvNotOwned; fail).
      { derive_footprint_info_basis oidx.
        assert (NoRqI oidx msgs)
          by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx).
        simpl_InvNotOwned.
      }
      { derive_footprint_info_basis oidx.
        assert (NoRqI oidx msgs)
          by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx).
        simpl_InvNotOwned.
      }
      { eapply InvNotOwned_enqMP_rq_valid; eauto.
        { solve_InvNotOwned. }
        { mred. }
        { assumption. }
      }

      END_SKIP_PROOF_ON *) admit.
  Qed.

  Theorem mesi_InvNotOwned_ok:
    InvReachable impl step_m InvNotOwned.
  Proof.
    eapply inv_reachable.
    - typeclasses eauto.
    - apply mesi_InvNotOwned_init.
    - apply mesi_InvNotOwned_step.
  Qed.

End InvNotOwned.

Definition CohRsE (oidx: IdxT) (msgs: MessagePool Msg) (cv: nat) :=
  MsgsP [((downTo oidx, (MRs, mesiRsE)),
          (fun idm => (valOf idm).(msg_value) = cv))] msgs.

Definition ObjCohDirE (ost: OState) :=
  ost#[owned] = false /\
  (mesiS <= ost#[status] \/ ost#[dir].(dir_st) = mesiE).

Definition InvDirE (topo: DTree) (st: State): Prop :=
  forall oidx pidx,
    parentIdxOf topo oidx = Some pidx ->
    ost <+- (st_oss st)@[oidx];
      orq <+- (st_orqs st)@[oidx];
      post <+- (st_oss st)@[pidx];
      porq <+- (st_orqs st)@[pidx];
      (ObjDirE porq post oidx ->
       (CohRsE oidx (st_msgs st) post#[val] /\
        (NoRsME oidx (st_msgs st) ->
         ObjCohDirE ost ->
         post#[val] = ost#[val]))).

Lemma ObjDirE_ObjDirME:
  forall orq ost cidx,
    ObjDirE orq ost cidx -> ObjDirME orq ost cidx.
Proof.
  intros.
  red in H; dest.
  red; repeat split; try assumption; solve_mesi.
Qed.

Section InvDirE.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma mesi_InvDirE_init:
    Invariant.InvInit impl (InvDirE topo).
  Proof.
    do 2 (red; simpl); intros.
    destruct (implOStatesInit tr)@[oidx] as [ost|] eqn:Host; simpl; auto.
    destruct (implORqsInit tr)@[oidx] as [orq|] eqn:Horq; simpl; auto.
    destruct (implOStatesInit tr)@[pidx] as [post|] eqn:Hpost; simpl; auto.
    destruct (implORqsInit tr)@[pidx] as [porq|] eqn:Hporq; simpl; auto.
    intros; exfalso.
    red in H0; dest.
    destruct (in_dec idx_dec pidx (c_li_indices cifc ++ c_l1_indices cifc)).
    - subst cifc; rewrite c_li_indices_head_rootOf in i by assumption.
      inv i.
      + rewrite implOStatesInit_value_root in Hpost by assumption.
        inv Hpost.
        simpl in *; solve_mesi.
      + rewrite implOStatesInit_value_non_root in Hpost by assumption.
        inv Hpost.
        simpl in *; solve_mesi.
    - rewrite implOStatesInit_None in Hpost by assumption.
      discriminate.
  Qed.

  Lemma mesi_InvDirE_ext_in:
    forall oss orqs msgs,
      InvDirE topo {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      InObjInds tr 0 {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        InvDirE topo {| st_oss := oss;
                        st_orqs := orqs;
                        st_msgs := enqMsgs eins msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H _ _ H2); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros; specialize (H H3); dest.
    split.
    - apply MsgsP_other_midx_enqMsgs; [assumption|].
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
    - intros; apply MsgsP_enqMsgs_inv in H5; auto.
  Qed.

  Lemma mesi_InvDirE_ext_out:
    forall oss orqs msgs,
      InvDirE topo {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      InObjInds tr 0 {| st_oss := oss; st_orqs := orqs; st_msgs := msgs |} ->
      forall (eouts: list (Id Msg)),
        ValidMsgsExtOut impl eouts ->
        InvDirE topo {| st_oss := oss;
                         st_orqs := orqs;
                         st_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H _ _ H2); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros; specialize (H H3); dest.
    split.
    - apply MsgsP_deqMsgs; assumption.
    - intros; apply MsgsP_other_midx_deqMsgs_inv in H5; [auto|].
      destruct H1.
      simpl; eapply DisjList_SubList; [eassumption|].
      eapply DisjList_comm, DisjList_SubList.
      + eapply SubList_trans;
          [|eapply tree2Topo_obj_chns_minds_SubList with (oidx:= oidx)].
        * solve_SubList.
        * specialize (H0 oidx); simpl in H0.
          rewrite Host in H0; simpl in H0.
          eassumption.
      + apply tree2Topo_minds_merss_disj.
  Qed.

  Lemma InvDirE_enqMP:
    forall oss orqs msgs,
      InvDirE topo {| st_oss:= oss; st_orqs:= orqs; st_msgs:= msgs |} ->
      forall midx msg,
        msg.(msg_id) <> mesiRsE ->
        InvDirE topo {| st_oss:= oss; st_orqs:= orqs;
                        st_msgs:= enqMP midx msg msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H _ _ H1); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros; specialize (H H2); dest.
    split.
    - apply MsgsP_other_msg_id_enqMP; [assumption|].
      simpl; intro Hx; destruct Hx; auto.
    - intros; apply MsgsP_enqMP_inv in H4; auto.
  Qed.

  Lemma InvDirE_enqMsgs:
    forall oss orqs msgs,
      InvDirE topo {| st_oss:= oss; st_orqs:= orqs; st_msgs:= msgs |} ->
      forall nmsgs,
        Forall (fun idm => (valOf idm).(msg_id) <> mesiRsE) nmsgs ->
        InvDirE topo {| st_oss:= oss; st_orqs:= orqs;
                        st_msgs:= enqMsgs nmsgs msgs |}.
  Proof.
    intros.
    generalize dependent msgs.
    induction nmsgs as [|[nmidx nmsg] nmsgs]; simpl; intros; auto.
    inv H0.
    apply IHnmsgs; auto.
    apply InvDirE_enqMP; assumption.
  Qed.

  Lemma InvDirE_deqMP:
    forall oss orqs msgs,
      InvDirE topo {| st_oss:= oss; st_orqs:= orqs; st_msgs:= msgs |} ->
      forall midx msg,
        FirstMP msgs midx msg ->
        msg.(msg_id) <> mesiRsM ->
        msg.(msg_id) <> mesiRsE ->
        InvDirE topo {| st_oss:= oss; st_orqs:= orqs;
                        st_msgs:= deqMP midx msgs |}.
  Proof.
    unfold InvDirE; simpl; intros.
    specialize (H _ _ H3).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros; specialize (H H4); dest.
    split.
    - apply MsgsP_deqMP; assumption.
    - intros; eapply MsgsP_other_msg_id_deqMP_inv in H6;
        [|eassumption|simpl; intro; intuition].
      auto.
  Qed.

  Lemma InvDirE_deqMsgs:
    forall oss orqs msgs,
      InvDirE topo {| st_oss:= oss; st_orqs:= orqs; st_msgs:= msgs |} ->
      forall rmsgs,
        Forall (FirstMPI msgs) rmsgs ->
        NoDup (idsOf rmsgs) ->
        Forall (fun idm => (valOf idm).(msg_id) <> mesiRsM /\
                           (valOf idm).(msg_id) <> mesiRsE) rmsgs ->
        InvDirE topo {| st_oss:= oss; st_orqs:= orqs;
                        st_msgs:= deqMsgs (idsOf rmsgs) msgs |}.
  Proof.
    unfold InvDirE; simpl; intros.
    specialize (H _ _ H3).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    destruct (orqs@[oidx]) as [orq|] eqn:Horq; simpl in *; auto.
    destruct (oss@[pidx]) as [post|] eqn:Hpost; simpl in *; auto.
    destruct (orqs@[pidx]) as [porq|] eqn:Hporq; simpl in *; auto.
    intros; specialize (H H4); dest.
    split.
    - apply MsgsP_deqMsgs; assumption.
    - intros; eapply MsgsP_other_msg_id_deqMsgs_inv in H6; try eassumption.
      + specialize (H5 H6 H7); dest; auto.
      + simpl.
        apply (DisjList_spec_1 idx_dec); intros.
        apply in_map_iff in H8; destruct H8 as [idm [? ?]].
        rewrite Forall_forall in H2; specialize (H2 _ H9); dest; subst.
        intro; dest_in; auto.
  Qed.

  Ltac solve_msg :=
    simpl;
    try match goal with
        | [H: msg_id ?rmsg = _ |- msg_id ?rmsg <> _] => rewrite H
        end;
    discriminate.

  Ltac solve_enqMsgs :=
    let idm := fresh "idm" in
    let Hin := fresh "H" in
    apply Forall_forall; intros idm Hin;
    apply in_map_iff in Hin; dest; subst;
    solve_msg.

  Ltac solve_deqMsgs_NoDup :=
    match goal with
    | [H: ValidMsgsIn _ ?msgs |- NoDup (idsOf ?msgs)] => apply H
    end.

  Ltac solve_deqMsgs_msg_id :=
    match goal with
    | [H: Forall (fun _ => msg_id _ = _) ?msgs |- Forall _ ?msgs] =>
      eapply Forall_impl; [|eapply H];
      simpl; intros; split; solve_msg
    end.

  Ltac simpl_InvDirE_msgs :=
    try match goal with
        | [Hr: idsOf _ = map fst ?rss |- context [map fst ?rss] ] => rewrite <-Hr
        end;
    repeat
      (first [apply InvDirE_enqMP; [|solve_msg..]
             |apply InvDirE_enqMsgs; [|solve_enqMsgs]
             |eapply InvDirE_deqMP; [|eassumption|solve_msg..]
             |apply InvDirE_deqMsgs; [|eassumption
                                      |solve_deqMsgs_NoDup
                                      |solve_deqMsgs_msg_id]
             |assumption]).

  Ltac disc_ObjDirE :=
    match goal with
    | [H: ObjDirE _ _ _ |- _] =>
      red in H; simpl in H; dest; subst
    end.

  Ltac disc_NoRsME :=
    repeat
      match goal with
      | [H: ValidMsgsIn _ _ |- _] => destruct H
      | [H: ValidMsgsOut _ _ |- _] => destruct H
      end;
    repeat
      match goal with
      | [H: NoRsME _ _ |- _] => disc_MsgsP H
      | [Hi: NoRsME _ ?msgs -> _ /\ _,  Hm: MsgsP _ ?msgs |- _] =>
        specialize (Hi Hm); dest
      end.

  Ltac disc :=
    repeat
      match goal with
      | [Hi: InvDirE _ _ |- InvDirE _ _] =>
        let Hp := fresh "H" in
        red; simpl; intros ? ? Hp;
        specialize (Hi _ _ Hp); simpl in Hi;
        mred; simpl;
        try (exfalso; eapply parentIdxOf_not_eq; subst topo; eauto; fail)
      | |- _ <+- _; _ => disc_bind_true
      | |- _ -> _ => intros
      | [Hi: ObjDirE _ _ _ -> _, Ho: ObjDirE _ _ _ |- _] =>
        specialize (Hi Ho); dest
      | [Hi: NoRsME _ _ -> _, Hm: NoRsME _ _ |- _] =>
        specialize (Hi Hm)
      | [Hi: ObjCohDirE ?ost -> _, Hm: ObjCohDirE ?ost |- _] =>
        specialize (Hi Hm)
      | [H: ?t = ?t -> _ |- _] => specialize (H eq_refl); dest
      end.

  Ltac solve_by_diff_dir :=
    intros;
    match goal with
    | [Hn: ObjDirE _ _ _ |- _] =>
      red in Hn; dest; simpl in *; solve_mesi
    end.

  Ltac solve_by_idx_false :=
    intros; subst topo; congruence.

  Ltac solve_by_NoRsME_false :=
    exfalso;
    match goal with
    | [Hn: NoRsME _ (enqMP ?midx ?msg ?msgs) |- _] =>
      specialize (Hn (midx, msg)
                     (InMP_or_enqMP
                        msgs (or_introl (conj eq_refl eq_refl))));
      red in Hn; unfold map in Hn;
      disc_caseDec Hn; auto
    end.

  Ltac solve_ObjCohDirE :=
    try assumption;
    match goal with
    | [H: ObjCohDirE _ |- _] =>
      red in H; dest; red; simpl in *
    end;
    try match goal with
        | [H: context [invalidate ?st] |- _] =>
          pose proof (invalidate_sound st)
        | |- context [invalidate ?st] =>
          pose proof (invalidate_sound st)
        end;
    intuition solve_mesi.

  Ltac solve_coh :=
    intros;
    match goal with
    | [H: _ -> _ -> fst ?lv = fst ?rv |- fst ?lv = fst ?rv] =>
      apply H; [disc_NoRsME; assumption|solve_ObjCohDirE]
    end.

  Ltac solve_by_ObjCohDirE_false :=
    intros;
    try match goal with
        | [H: context [invalidate ?st] |- _] =>
          pose proof (invalidate_sound st)
        | |- context [invalidate ?st] =>
          pose proof (invalidate_sound st)
        end;
    match goal with
    | [H: ObjCohDirE _ |- _] =>
      red in H; simpl in *; dest; solve [congruence|solve_mesi]
    end.

  Ltac solve_valid :=
    split; [solve_MsgsP|solve_coh].

  Ltac solve_by_child_downlock_to_parent oidx :=
    exfalso;
    disc_MsgConflictsInv oidx;
    match goal with
    | [Hp: ParentLockFreeConflicts oidx ?porq ?orq,
           Ho: ?orq@[downRq] = None,
               Hpo: ?porq@[downRq] = Some _ |- _] =>
      specialize (Hp Ho); rewrite Hpo in Hp;
      simpl in Hp; auto
    end.

  Ltac solve_by_NoRsSI_false :=
    exfalso;
    match goal with
    | [Hn: NoRsSI _ ?msgs, Hf: FirstMPI ?msgs (?midx, ?msg) |- _] =>
      specialize (Hn (midx, msg) (FirstMP_InMP Hf));
      solve_MsgsP_false Hn;
      auto
    end.

  Lemma mesi_InvDirE_step:
    Invariant.InvStep impl step_m (InvDirE topo).
  Proof. (* SKIP_PROOF_ON
    red; intros.
    pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (mesi_InObjInds H) as Hioi.
    pose proof (mesi_MsgConflictsInv
                  (@mesi_RootChnInv_ok _ Htr) H) as Hpmcf.
    pose proof (mesi_InvWBDir_ok H) as Hwd.
    pose proof (MesiDownLockInv_ok H) as Hmdl.
    pose proof (mesi_InvL1DirI_ok H) as Hl1d.
    pose proof (mesi_InvDirME_ok H) as Hdme.
    inv H1; [assumption
            |apply mesi_InvDirE_ext_in; auto
            |apply mesi_InvDirE_ext_out; auto
            |].

    simpl in H2; destruct H2; [subst|apply in_app_or in H1; destruct H1].

    - (*! Cases for the main memory *)

      (** Abstract the root. *)
      assert (In (rootOf (fst (tree2Topo tr 0)))
                 (c_li_indices (snd (tree2Topo tr 0)))) as Hin.
      { rewrite c_li_indices_head_rootOf by assumption.
        left; reflexivity.
      }

      remember (rootOf (fst (tree2Topo tr 0))) as oidx; clear Heqoidx.

      (** Do case analysis per a rule. *)
      apply in_app_or in H3; destruct H3.

      1: { (** Rules per a child *)
        apply concat_In in H1; destruct H1 as [crls [? ?]].
        apply in_map_iff in H1; destruct H1 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in.

        { (* [liGetSImmS] *)
          disc_rule_conds_ex; disc.
          { solve_valid. }
          { solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { (* [liGetSImmME] *)
          disc_rule_conds_ex; disc.
          { solve_valid. }
          { disc_ObjDirE.
            split; intros.
            { apply MsgsP_enqMP.
              { derive_child_idx_in oidx0.
                disc_MsgConflictsInv oidx0.
                apply MsgsNotExist_MsgsP; simpl.
                apply MsgsP_deqMP.
                solve_MsgsNotExist_base.
                solve_RsDown_by_rqUp oidx0.
              }
              { red; unfold map.
                rewrite caseDec_head_eq by reflexivity.
                reflexivity.
              }
            }
            { solve_by_NoRsME_false. }
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { (* [liGetSRqUpDownME] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          disc_ObjDirE; mred.
        }

        { (* [liGetMImm] *)
          disc_rule_conds_ex; disc.
          { solve_valid. }
          { solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { (* [liGetMRqUpDownME] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          disc_ObjDirE; mred.
        }
        { (* [liGetMRqUpDownS] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          disc_ObjDirE; mred.
        }

        { (* [liInvImmI] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        }

        { (* [liInvImmS00] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          { solve_valid. }
          { solve_by_diff_dir. }
        }

        { (* [liInvImmS01] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          { split; [solve_MsgsP|solve_by_ObjCohDirE_false]. }
          { solve_by_diff_dir. }
        }

        { (* [liInvImmS1] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          { solve_valid. }
          { solve_by_diff_dir. }
        }

        { (* [liInvImmE] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          { split; [solve_MsgsP|disc_getDir; solve_coh]. }
          { solve_by_diff_dir. }
        }

        { (* [liInvImmWBI] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        }

        { (* [liInvImmWBS1] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          { solve_valid. }
          { solve_by_diff_dir. }
        }

        { (* [liInvImmWBME] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          { split; [solve_MsgsP|solve_by_ObjCohDirE_false]. }
          { solve_by_diff_dir. }
        }

      }

      dest_in.

      { (* [liDownSRsUpDownME] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        simpl_InvDirE_msgs; disc.
        { split; [solve_MsgsP|solve_by_ObjCohDirE_false]. }
        { solve_by_diff_dir. }
      }

      { (* [liDownIRsUpDownS] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        simpl_InvDirE_msgs; disc.
        { solve_valid. }
        { solve_by_diff_dir. }
      }

      { (* [liDownIRsUpDownME] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        simpl_InvDirE_msgs; disc.
        { solve_valid. }
        { solve_by_diff_dir. }
      }

    - (*! Cases for Li caches *)

      (** Derive some necessary information: each Li has a parent. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst; simpl in *.

      pose proof (c_li_indices_tail_has_parent Htr _ _ H2).
      destruct H1 as [pidx [? ?]].
      pose proof (Htn _ _ H4); dest.

      (** Do case analysis per a rule. *)
      apply in_app_or in H3; destruct H3.

      1: { (** Rules per a child *)
        apply concat_In in H3; destruct H3 as [crls [? ?]].
        apply in_map_iff in H3; destruct H3 as [cidx [? ?]]; subst.

        (** Derive that the child has the parent. *)
        assert (parentIdxOf (fst (tree2Topo tr 0)) cidx = Some oidx)
          by (apply subtreeChildrenIndsOf_parentIdxOf; auto).

        dest_in.

        { (* [liGetSImmS] *)
          disc_rule_conds_ex; disc.
          { solve_valid. }
          { solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { (* [liGetSImmME] *)
          disc_rule_conds_ex; disc.
          { solve_valid. }
          { disc_ObjDirE.
            split; intros.
            { apply MsgsP_enqMP.
              { derive_child_idx_in oidx0.
                disc_MsgConflictsInv oidx0.
                apply MsgsNotExist_MsgsP; simpl.
                apply MsgsP_deqMP.
                solve_MsgsNotExist_base.
                solve_RsDown_by_rqUp oidx0.
              }
              { red; unfold map.
                rewrite caseDec_head_eq by reflexivity.
                reflexivity.
              }
            }
            { solve_by_NoRsME_false. }
          }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { (* [liGetSRqUpUp] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs.
          disc; red in H18; mred.
          specialize (H0 H18); dest.
          solve_valid.
        }

        { (* [liGetSRqUpDownME] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          disc_ObjDirE; mred.
        }

        { (* [liGetMImm] *)
          disc_rule_conds_ex; disc.
          { solve_valid. }
          { solve_by_diff_dir. }
          { destruct (idx_dec cidx oidx0); subst.
            { solve_by_idx_false. }
            { solve_valid. }
          }
        }

        { (* [liGetMRqUpUp] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs.
          disc; red in H18; mred.
          specialize (H0 H18); dest.
          solve_valid.
        }

        { (* [liGetMRqUpDownME] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          disc_ObjDirE; mred.
        }
        { (* [liGetMRqUpDownS] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          disc_ObjDirE; mred.
        }

        { (* [liInvImmI] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        }

        { (* [liInvImmS00] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          { solve_valid. }
          { solve_by_diff_dir. }
        }

        { (* [liInvImmS01] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          { split; [solve_MsgsP|solve_by_ObjCohDirE_false]. }
          { solve_by_diff_dir. }
        }

        { (* [liInvImmS1] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          { solve_valid. }
          { solve_by_diff_dir. }
        }

        { (* [liInvImmE] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          { split; [solve_MsgsP|disc_getDir; solve_coh]. }
          { solve_by_diff_dir. }
        }

        { (* [liInvImmWBI] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        }

        { (* [liInvImmWBS1] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          { solve_valid. }
          { solve_by_diff_dir. }
        }

        { (* [liInvImmWBME] *)
          disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
          { split; [solve_MsgsP|solve_by_ObjCohDirE_false]. }
          { solve_by_diff_dir. }
        }

      }

      dest_in.

      { (* [liGetSRsDownDownS] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        disc.
        { split; [solve_MsgsP|].

          subst topo; disc_rule_conds_ex.
          intros.

          (** TODO: make an Ltac [disc_InvDirME] .. *)
          move Hdme at bottom.
          red in Hdme; simpl in Hdme.
          specialize (Hdme _ _ H4).
          disc_rule_conds_ex.
          disc_NoRsME.
          specialize (Hdme (ObjDirE_ObjDirME H29)).
          specialize (Hdme H31); dest.

          solve_by_NoRsSI_false.
        }
        { solve_by_diff_dir. }
        { destruct (idx_dec cidx oidx0); subst.
          { solve_by_idx_false. }
          { solve_valid. }
        }
      }

      { (* [liGetSRsDownDownE] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        disc.
        { split; [solve_MsgsP|].
          (* pulling a coherence value from the [mesiRsE] message. *)
          intros.
          move H0 at bottom.
          specialize (H0 _ (FirstMP_InMP H21)).
          red in H0.
          unfold map in H0.
          rewrite caseDec_head_eq in H0 by (unfold sigOf; simpl; congruence).
          auto.
        }
        { disc_ObjDirE.
          split; intros.
          { apply MsgsP_enqMP.
            { derive_child_idx_in oidx0.
              disc_MsgConflictsInv oidx0.
              apply MsgsNotExist_MsgsP; simpl.
              apply MsgsP_deqMP.
              solve_MsgsNotExist_base.
              solve_RsDown_by_parent_lock oidx0.
            }
            { red; unfold map.
              rewrite caseDec_head_eq by reflexivity.
              reflexivity.
            }
          }
          { solve_by_NoRsME_false. }
        }
        { destruct (idx_dec cidx oidx0); subst.
          { solve_by_idx_false. }
          { solve_valid. }
        }
      }

      { (* [liDownSRsUpDownME] *)
        disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        { split; [solve_MsgsP|solve_by_ObjCohDirE_false]. }
        { solve_by_diff_dir. }
      }

      { (* [liDownSImm] *)
        disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        exfalso.
        subst topo; disc_rule_conds_ex.
        disc_ObjDirE.
        remember (dir_excl _) as oidx; clear Heqoidx.
        derive_parent_downlock_by_RqDown oidx.
        auto.
      }

      { (* [liDownSRqDownDownME] *)
        disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        disc_ObjDirE; mred.
      }

      { (* [liDownSRsUpUp] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        simpl_InvDirE_msgs; disc.
        { disc_ObjDirE.
          remember (dir_excl _) as oidx; clear Heqoidx.
          disc_MsgConflictsInv oidx.

          solve_by_child_downlock_to_parent oidx.
        }
        { solve_by_diff_dir. }
      }

      { (* [liGetMRsDownDownDirI] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        disc.
        { split; [solve_MsgsP|solve_by_ObjCohDirE_false]. }
        { solve_by_diff_dir. }
        { destruct (idx_dec cidx oidx0); subst.
          { solve_by_idx_false. }
          { solve_valid. }
        }
      }

      { (* [liGetMRsDownRqDownDirS] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        simpl_InvDirE_msgs; disc.
        { split; [solve_MsgsP|solve_by_ObjCohDirE_false]. }
        { solve_by_diff_dir. }
        { solve_valid. }
      }

      { (* [liDownIRsUpDownS] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        simpl_InvDirE_msgs; disc.
        { solve_valid. }
        { solve_by_diff_dir. }
      }

      { (* [liDownIRsUpDownME] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        simpl_InvDirE_msgs; disc.
        { solve_valid. }
        { solve_by_diff_dir. }
      }

      { (* [liDownIImmS] *)
        disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        exfalso.
        subst topo; disc_rule_conds_ex.
        disc_ObjDirE.
        remember (dir_excl _) as oidx; clear Heqoidx.
        derive_parent_downlock_by_RqDown oidx.
        auto.
      }

      { (* [liDownIImmME] *)
        disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        exfalso.
        subst topo; disc_rule_conds_ex.
        disc_ObjDirE.
        remember (dir_excl _) as oidx; clear Heqoidx.
        derive_parent_downlock_by_RqDown oidx.
        auto.
      }

      { (* [liDownIRqDownDownDirS] *)
        disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        disc_ObjDirE; mred.
      }
      { (* [liDownIRqDownDownDirME] *)
        disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        disc_ObjDirE; mred.
      }
      { (* [liDownIRqDownDownDirMES] *)
        disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        disc_ObjDirE; mred.
      }

      { (* [liDownIRsUpUpS] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        simpl_InvDirE_msgs; disc.
        { subst topo; disc_rule_conds_ex.
          disc_ObjDirE.
          remember (dir_excl _) as oidx; clear Heqoidx.
          disc_MsgConflictsInv oidx.
          solve_by_child_downlock_to_parent oidx.
        }
        { solve_by_diff_dir. }
      }

      { (* [liDownIRsUpUpME] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        simpl_InvDirE_msgs; disc.
        { subst topo; disc_rule_conds_ex.
          disc_ObjDirE.
          remember (dir_excl _) as oidx; clear Heqoidx.
          disc_MsgConflictsInv oidx.
          solve_by_child_downlock_to_parent oidx.
        }
        { solve_by_diff_dir. }
      }

      { (* [liDownIRsUpUpMES] *)
        disc_rule_conds_ex.
        disc_MesiDownLockInv oidx Hmdl.
        simpl_InvDirE_msgs; disc.
        { subst topo; disc_rule_conds_ex.
          disc_ObjDirE.
          remember (dir_excl _) as oidx; clear Heqoidx.
          disc_MsgConflictsInv oidx.
          solve_by_child_downlock_to_parent oidx.
        }
        { solve_by_diff_dir. }
      }

      { (* [liInvRqUpUp] *)
        disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        disc_ObjDirE; solve_mesi.
      }

      { (* [liInvRqUpUpWB] *)
        disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        disc_ObjDirE; solve_mesi.
      }

      { (* [liInvRsDownDown] *)
        disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_InvWBDir oidx.
        assert (ObjInvRs oidx msgs) as Hirs.
        { do 2 red.
          eexists; split; [apply FirstMP_InMP; eassumption|].
          unfold sigOf; simpl; congruence.
        }
        specialize (Hwd (or_intror (or_intror Hirs))); clear Hirs.

        simpl_InvDirE_msgs; disc.
        { split; [solve_MsgsP|solve_by_ObjCohDirE_false]. }
        { disc_ObjDirE; solve_mesi. }
      }

      { (* [liPushImm] *)
        disc_rule_conds_ex; disc; solve_valid.
      }

    - (*! Cases for L1 caches *)

      (** Derive some necessary information: each Li has a parent. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst.

      pose proof (c_l1_indices_has_parent Htr _ _ H2).
      destruct H1 as [pidx [? ?]].
      pose proof (Htn _ _ H4); dest.

      (** Discharge an invariant that holds only for L1 caches. *)
      red in Hl1d; simpl in Hl1d.
      rewrite Forall_forall in Hl1d; specialize (Hl1d _ H2).
      simpl in H5; rewrite H5 in Hl1d; simpl in Hl1d.

      (** Do case analysis per a rule. *)
      dest_in.

      { disc_rule_conds_ex; simpl_InvDirE_msgs; disc. }

      { disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        red in H16; mred; specialize (H0 H16); dest.
        solve_valid.
      }

      { disc_rule_conds_ex; simpl_InvDirE_msgs.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        disc.
        { split; [solve_MsgsP|].

          subst topo; disc_rule_conds_ex.
          intros.

          (** TODO: make an Ltac [disc_InvDirME] .. *)
          move Hdme at bottom.
          red in Hdme; simpl in Hdme.
          specialize (Hdme _ _ H4).
          disc_rule_conds_ex.
          specialize (Hdme (ObjDirE_ObjDirME H28)).
          specialize (Hdme H30); dest.

          solve_by_NoRsSI_false.
        }
        { solve_by_diff_dir. }
      }

      { disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        disc.
        { split; [solve_MsgsP|].
          (* pulling a coherence value from the [mesiRsE] message. *)
          intros.
          move H0 at bottom.
          specialize (H0 _ (FirstMP_InMP H21)).
          red in H0.
          unfold map in H0.
          rewrite caseDec_head_eq in H0 by (unfold sigOf; simpl; congruence).
          auto.
        }
        { disc_ObjDirE; solve_mesi. }
        { destruct (idx_dec (l1ExtOf oidx) oidx0); subst.
          { exfalso.
            subst topo.
            rewrite tree2Topo_l1_ext_parent in H3 by assumption.
            congruence.
          }
          { solve_valid. }
        }
      }

      { disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        exfalso.
        subst topo; disc_rule_conds_ex.
        disc_ObjDirE.
        remember (dir_excl _) as oidx; clear Heqoidx.
        derive_parent_downlock_by_RqDown oidx.
        auto.
      }

      { disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        { split; [solve_MsgsP|solve_by_ObjCohDirE_false]. }
        { solve_by_diff_dir. }
      }

      { disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        { split; [solve_MsgsP|solve_by_ObjCohDirE_false]. }
        { solve_by_diff_dir. }
      }

      { disc_rule_conds_ex; simpl_InvDirE_msgs.
        disc; red in H16; mred.
        specialize (H0 H16); dest.
        solve_valid.
      }

      { disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_child_chns cidx.
        disc_rule_conds_ex.
        disc.
        { split; [solve_MsgsP|solve_by_ObjCohDirE_false]. }
        { solve_by_diff_dir. }
        { destruct (idx_dec (l1ExtOf oidx) oidx0); subst.
          { exfalso.
            subst topo.
            rewrite tree2Topo_l1_ext_parent in H3 by assumption.
            congruence.
          }
          { solve_valid. }
        }
      }

      { disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        exfalso.
        subst topo; disc_rule_conds_ex.
        disc_ObjDirE.
        remember (dir_excl _) as oidx; clear Heqoidx.
        derive_parent_downlock_by_RqDown oidx.
        auto.
      }

      { disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        exfalso.
        subst topo; disc_rule_conds_ex.
        disc_ObjDirE.
        remember (dir_excl _) as oidx; clear Heqoidx.
        derive_parent_downlock_by_RqDown oidx.
        auto.
      }

      { disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        disc_ObjDirE; solve_mesi.
      }

      { disc_rule_conds_ex; simpl_InvDirE_msgs; disc.
        disc_ObjDirE; solve_mesi.
      }

      { disc_rule_conds_ex.
        derive_footprint_info_basis oidx.
        derive_InvWBDir oidx.
        assert (ObjInvRs oidx msgs) as Hirs.
        { do 2 red.
          eexists; split; [apply FirstMP_InMP; eassumption|].
          unfold sigOf; simpl; congruence.
        }
        specialize (Hwd (or_intror (or_intror Hirs))); clear Hirs.

        simpl_InvDirE_msgs; disc.
        { split; [solve_MsgsP|solve_by_ObjCohDirE_false]. }
        { disc_ObjDirE; solve_mesi. }
      }

      END_SKIP_PROOF_ON *) admit.
  Qed.

  Theorem mesi_InvDirE_ok:
    InvReachable impl step_m (InvDirE topo).
  Proof.
    eapply inv_reachable.
    - typeclasses eauto.
    - apply mesi_InvDirE_init.
    - apply mesi_InvDirE_step.
  Qed.

End InvDirE.

Definition InvNWB (topo: DTree) (st: State): Prop :=
  forall oidx pidx,
    parentIdxOf topo oidx = Some pidx ->
    ost <+- (st_oss st)@[oidx];
      orq <+- (st_orqs st)@[oidx];
      post <+- (st_oss st)@[pidx];
      porq <+- (st_orqs st)@[pidx];
      (ObjDirE porq post oidx ->
       ObjInvRq oidx (st_msgs st) ->
       NoRsI oidx (st_msgs st) /\ mesiS <= ost#[status] /\
       ost#[val] = post#[val]).

Section InvNWB.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Theorem mesi_InvNWB_ok:
    InvReachable impl step_m (InvNWB topo).
  Proof.
    red; intros.
    pose proof (mesi_InObjInds H) as Hoin.
    pose proof (mesi_MsgConflictsInv (@mesi_RootChnInv_ok _ Htr) H) as Hmcf.
    pose proof (mesi_InvDirME_ok H) as Hdme.
    pose proof (mesi_InvNotOwned_ok H) as Hno.
    pose proof (mesi_InvDirE_ok H) as Hde.
    pose proof (mesi_InvWBDir_ok H) as Hwd.

    red; intros.
    specialize (Hoin oidx).
    specialize (Hmcf oidx).
    specialize (Hdme _ _ H0).
    specialize (Hno oidx).
    specialize (Hde _ _ H0).
    specialize (Hwd oidx).

    destruct (st_oss ist)@[oidx] as [ost|] eqn:Host; simpl in *; auto.
    destruct (st_orqs ist)@[oidx] as [orq|] eqn:Horq; simpl in *; auto.
    destruct (st_oss ist)@[pidx] as [post|] eqn:Hpost; simpl in *; auto.
    destruct (st_orqs ist)@[pidx] as [porq|] eqn:Hporq; simpl in *; auto.

    specialize (Hmcf _ Hoin eq_refl); dest.
    intros.
    specialize (Hwd (or_intror (or_introl H7))).
    specialize (Hno H7).
    specialize (Hde H6).
    destruct Hde as [_ Hde].
    specialize (Hdme (ObjDirE_ObjDirME H6)).

    assert (NoRsME oidx (st_msgs ist)) as Hnrs.
    { destruct H7 as [[rqUp rqm] ?]; dest; inv H8.
      apply not_MsgExistsSig_MsgsNotExist.
      intros; dest_in.
      { destruct H9 as [[rsDown rsm] ?]; dest; inv H9.
        specialize (H2 (rqUpFrom oidx, rqm) eq_refl H7); dest.
        eapply H10 with (rsDown:= (downTo oidx, rsm)); eauto.
      }
      { destruct H9 as [[rsDown rsm] ?]; dest; inv H9.
        specialize (H2 (rqUpFrom oidx, rqm) eq_refl H7); dest.
        eapply H10 with (rsDown:= (downTo oidx, rsm)); eauto.
      }
    }

    specialize (Hdme Hnrs); destruct Hdme as [Hnrsi Hdme].

    assert (mesiS <= ost#[status]) as Hs.
    { specialize (Hdme ltac:(solve_mesi)).
      destruct Hdme; dest; simpl in *; solve_mesi.
    }

    assert (ObjCohDirE ost) as Hode.
    { split; [assumption|left; assumption]. }
    specialize (Hde Hnrs Hode).

    repeat split.
    - clear -Hnrsi.
      do 3 red; intros.
      specialize (Hnrsi _ H).
      red in Hnrsi.
      rewrite map_trans in Hnrsi; do 2 rewrite map_cons in Hnrsi.
      red in Hnrsi.
      do 2 (destruct (sig_dec _ _); [exfalso; auto|]).
      clear Hnrsi.
      red.
      rewrite map_trans, map_cons.
      rewrite caseDec_head_neq by assumption.
      simpl; auto.
    - assumption.
    - apply eq_sym; assumption.
  Qed.

End InvNWB.
