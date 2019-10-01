Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsInvMsg RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Require Import Ex.Mesi.MesiInv.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Mesi.ImplOStateIfc.

Definition InvWBDir (st: MState): Prop :=
  forall oidx,
    ost <+- (bst_oss st)@[oidx];
      ((ObjInvWRq oidx (bst_msgs st) \/ ObjInvRq oidx (bst_msgs st)) ->
       ost#[dir].(dir_st) = mesiI).

(** NOTE: [InvWBCoh] requires [InvWBDir] during the proof *)
Definition InvWBCoh (st: MState): Prop :=
  forall oidx,
    ost <+- (bst_oss st)@[oidx];
      CohInvRq oidx ost (bst_msgs st).

Section InvWBDir.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma mesi_InvWBDir_init:
    Invariant.InvInit impl InvWBDir.
  Proof.
    do 2 (red; simpl).
    intros.
    destruct (implOStatesInit tr)@[oidx] as [orq|] eqn:Host; simpl; auto.
    intros.
    exfalso; destruct H.
    - destruct H as [idm [? ?]].
      do 2 red in H; dest_in.
    - destruct H as [idm [? ?]].
      do 2 red in H; dest_in.
  Qed.      

  Lemma mesi_InvWBDir_ext_in:
    forall oss orqs msgs,
      InvWBDir {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        InvWBDir {| bst_oss := oss; bst_orqs := orqs; bst_msgs := enqMsgs eins msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H oidx); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    intros.
    destruct H2.
    - destruct H2 as [idm [? ?]].
      apply InMP_enqMsgs_or in H2.
      destruct H2; [|apply H; left; do 2 red; eauto].
      apply in_map with (f:= idOf) in H2; simpl in H2.
      apply H1 in H2; simpl in H2.
      exfalso; eapply DisjList_In_1.
      + apply tree2Topo_minds_merqs_disj.
      + eassumption.
      + eapply tree2Topo_obj_chns_minds_SubList.
        * specialize (H0 oidx); simpl in H0.
          rewrite Host in H0; simpl in H0.
          eassumption.
        * destruct idm as [midx msg]; inv H3.
          simpl; tauto.
    - destruct H2 as [idm [? ?]].
      apply InMP_enqMsgs_or in H2.
      destruct H2; [|apply H; right; do 2 red; eauto].
      apply in_map with (f:= idOf) in H2; simpl in H2.
      apply H1 in H2; simpl in H2.
      exfalso; eapply DisjList_In_1.
      + apply tree2Topo_minds_merqs_disj.
      + eassumption.
      + eapply tree2Topo_obj_chns_minds_SubList.
        * specialize (H0 oidx); simpl in H0.
          rewrite Host in H0; simpl in H0.
          eassumption.
        * destruct idm as [midx msg]; inv H3.
          simpl; tauto.
  Qed.

  Lemma mesi_InvWBDir_ext_out:
    forall oss orqs msgs,
      InvWBDir {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall (eouts: list (Id Msg)),
        InvWBDir {| bst_oss := oss;
                 bst_orqs := orqs;
                 bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H oidx); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    intros.
    destruct H1.
    - destruct H1 as [idm [? ?]].
      apply InMP_deqMsgs in H1.
      apply H; left; do 2 red; eauto.
    - destruct H1 as [idm [? ?]].
      apply InMP_deqMsgs in H1.
      apply H; right; do 2 red; eauto.
  Qed.

  Lemma InvWBDir_no_update:
    forall oss orqs msgs,
      InvWBDir {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall oidx (post nost: OState),
        oss@[oidx] = Some post ->
        nost#[dir].(dir_st) = post#[dir].(dir_st) ->
        InvWBDir {| bst_oss:= oss +[oidx <- nost];
                    bst_orqs:= orqs; bst_msgs:= msgs |}.
  Proof.
    unfold InvWBDir; simpl; intros.
    mred; simpl; auto.
    specialize (H oidx).
    rewrite H0 in H; simpl in H.
    intros.
    rewrite H1; auto.
  Qed.

  Lemma InvWBDir_update_status_NoRqI:
    forall oss orqs msgs,
      InvWBDir {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall oidx (ost: OState),
        NoRqI oidx msgs ->
        InvWBDir {| bst_oss:= oss +[oidx <- ost];
                    bst_orqs:= orqs; bst_msgs:= msgs |}.
  Proof.
    unfold InvWBDir; simpl; intros.
    mred; simpl; auto.
    intros.
    exfalso; destruct H1.
    all: eapply MsgExistsSig_MsgsNotExist_false; try eassumption;
      simpl; tauto.
  Qed.

  Lemma InvWBDir_enqMP_valid:
    forall oss orqs msgs,
      InvWBDir {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall oidx ost midx msg,
        oss@[oidx] = Some ost ->
        ost#[dir].(dir_st) = mesiI ->
        midx = rqUpFrom oidx ->
        msg.(msg_id) = mesiInvWRq \/ msg.(msg_id) = mesiInvRq ->
        InvWBDir {| bst_oss:= oss; bst_orqs:= orqs;
                    bst_msgs:= enqMP midx msg msgs |}.
  Proof.
    unfold InvWBDir; simpl; intros.
    destruct (idx_dec oidx0 oidx); subst.
    - specialize (H oidx).
      rewrite H0 in *; simpl in *.
      intros; auto.
    - specialize (H oidx0).
      destruct (oss@[oidx0]) as [ost0|]; simpl in *; auto.
      intros.
      destruct H2.
      + destruct H2 as [idm [? ?]].
        apply InMP_enqMP_or in H2; destruct H2.
        * dest; inv H4; rewrite H2 in H7; inv H7.
          exfalso; auto.
        * apply H; left; do 2 red; eauto.
      + destruct H2 as [idm [? ?]].
        apply InMP_enqMP_or in H2; destruct H2.
        * dest; inv H4; rewrite H2 in H7; inv H7.
          exfalso; auto.
        * apply H; right; do 2 red; eauto.
  Qed.

  Lemma InvWBDir_other_msg_id_enqMP:
    forall oss orqs msgs,
      InvWBDir {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx msg,
        msg.(msg_id) <> mesiInvWRq ->
        msg.(msg_id) <> mesiInvRq ->
        InvWBDir {| bst_oss:= oss; bst_orqs:= orqs;
                    bst_msgs:= enqMP midx msg msgs |}.
  Proof.
    unfold InvWBDir; simpl; intros.
    specialize (H oidx).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    intros.
    destruct H2.
    - destruct H2 as [idm [? ?]].
      apply InMP_enqMP_or in H2; destruct H2.
      + dest; subst; inv H3; exfalso; auto.
      + apply H; left; do 2 red; eauto.
    - destruct H2 as [idm [? ?]].
      apply InMP_enqMP_or in H2; destruct H2.
      + dest; subst; inv H3; exfalso; auto.
      + apply H; right; do 2 red; eauto.
  Qed.

  Lemma InvWBDir_other_msg_id_enqMsgs:
    forall oss orqs msgs,
      InvWBDir {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall nmsgs,
        Forall (fun idm => (valOf idm).(msg_id) <> mesiInvWRq /\
                           (valOf idm).(msg_id) <> mesiInvRq) nmsgs ->
        InvWBDir {| bst_oss:= oss; bst_orqs:= orqs;
                    bst_msgs:= enqMsgs nmsgs msgs |}.
  Proof.
    intros.
    generalize dependent msgs.
    induction nmsgs as [|[nmidx nmsg] nmsgs]; simpl; intros; auto.
    inv H0; dest.
    apply IHnmsgs; auto.
    apply InvWBDir_other_msg_id_enqMP; assumption.
  Qed.

  Lemma InvWBDir_deqMP:
    forall oss orqs msgs,
      InvWBDir {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx,
        InvWBDir {| bst_oss:= oss; bst_orqs:= orqs;
                    bst_msgs:= deqMP midx msgs |}.
  Proof.
    unfold InvWBDir; simpl; intros.
    specialize (H oidx).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    intros.
    destruct H0.
    - destruct H0 as [idm [? ?]].
      apply InMP_deqMP in H0.
      apply H; left; do 2 red; eauto.
    - destruct H0 as [idm [? ?]].
      apply InMP_deqMP in H0.
      apply H; right; do 2 red; eauto.
  Qed.

  Lemma InvWBDir_deqMsgs:
    forall oss orqs msgs,
      InvWBDir {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall minds,
        InvWBDir {| bst_oss:= oss; bst_orqs:= orqs;
                    bst_msgs:= deqMsgs minds msgs |}.
  Proof.
    unfold InvWBDir; simpl; intros.
    specialize (H oidx).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    intros.
    destruct H0.
    - destruct H0 as [idm [? ?]].
      apply InMP_deqMsgs in H0.
      apply H; left; do 2 red; eauto.
    - destruct H0 as [idm [? ?]].
      apply InMP_deqMsgs in H0.
      apply H; right; do 2 red; eauto.
  Qed.

  Ltac simpl_InvWBDir_enqMP :=
    simpl;
    try match goal with
        | [H: msg_id ?rmsg = _ |- msg_id ?rmsg <> _] => rewrite H
        end;
    discriminate.

  Ltac simpl_InvWBDir_enqMsgs :=
    let idm := fresh "idm" in
    let Hin := fresh "H" in
    apply Forall_forall; intros idm Hin;
    apply in_map_iff in Hin; dest; subst;
    split; simpl_InvWBDir_enqMP.

  Ltac simpl_InvWBDir :=
    repeat
      (first [apply InvWBDir_other_msg_id_enqMP; [|simpl_InvWBDir_enqMP..]
             |apply InvWBDir_other_msg_id_enqMsgs; [|simpl_InvWBDir_enqMsgs]
             |apply InvWBDir_deqMP
             |apply InvWBDir_deqMsgs
             |apply InvWBDir_update_status_NoRqI; [|assumption]
             |eapply InvWBDir_no_update; [|eauto; fail..]
             |assumption]).

  Ltac solve_InvWBDir :=
    let oidx := fresh "oidx" in
    red; simpl; intros oidx;
    match goal with
    | [Hi: InvWBDir _ |- _] =>
      specialize (Hi oidx); simpl in Hi;
      mred; simpl;
      let Hinv := fresh "H" in
      intros Hinv;
      specialize (Hi Hinv)
    end;
    solve_mesi.

  Lemma mesi_InvWBDir_step:
    Invariant.InvStep impl step_m InvWBDir.
  Proof.
    red; intros.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (mesi_InObjInds H) as Hioi.
    pose proof (mesi_MsgConflictsInv
                  (@mesi_RootChnInv_ok _ Htr) H) as Hpmcf.
    pose proof (MesiDownLockInv_ok H) as Hmdl.
    inv H1; [assumption
            |apply mesi_InvWBDir_ext_in; auto
            |apply mesi_InvWBDir_ext_out; auto
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

        all: try (simpl_InvWBDir; fail).
        all: try (assert (NoRqI oidx msgs)
                   by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx);
                  simpl_InvWBDir).
      }

      dest_in.
      { disc_rule_conds_ex.
        derive_MesiDownLockInv oidx.
        simpl_InvWBDir; solve_InvWBDir.
      }
      { disc_rule_conds_ex.
        derive_MesiDownLockInv oidx.
        simpl_InvWBDir; solve_InvWBDir.
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

        all: try (simpl_InvWBDir; fail).
        all: try (assert (NoRqI oidx msgs)
                   by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx);
                  simpl_InvWBDir).
      }

      dest_in; disc_rule_conds_ex.

      all: try (simpl_InvWBDir; fail).
      all: try (derive_footprint_info_basis oidx;
                assert (NoRqI oidx msgs)
                  by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx);
                simpl_InvWBDir).
      all: try (simpl_InvWBDir; solve_InvWBDir; fail).
      all: try (derive_MesiDownLockInv oidx;
                simpl_InvWBDir; solve_InvWBDir; fail).
      { eapply InvWBDir_enqMP_valid; eauto.
        { solve_InvWBDir. }
        { mred. }
        { assumption. }
      }
      { eapply InvWBDir_enqMP_valid; eauto.
        { solve_InvWBDir. }
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

      (** Do case analysis per a rule. *)
      dest_in; disc_rule_conds_ex.

      all: try (simpl_InvWBDir; fail).
      { eapply InvWBDir_enqMP_valid; eauto.
        { solve_InvWBDir. }
        { mred. }
        { assumption. }
      }
      { eapply InvWBDir_enqMP_valid; eauto.
        { solve_InvWBDir. }
        { mred. }
        { assumption. }
      }

  Qed.

  Theorem mesi_InvWBDir_ok:
    InvReachable impl step_m InvWBDir.
  Proof.
    apply inv_reachable.
    - apply mesi_InvWBDir_init.
    - apply mesi_InvWBDir_step.
  Qed.

End InvWBDir.

Ltac derive_InvWBDir oidx :=
  match goal with
  | [Hi: InvWBDir _ |- _] =>
    specialize (Hi oidx); simpl in Hi;
    repeat
      match type of Hi with
      | _ <+- ?ov; _ =>
        match goal with
        | [Hv: ov = Some _ |- _] => rewrite Hv in Hi; simpl in Hi
        end
      end
  end.

Section InvWBCoh.
  Variable (tr: tree).
  Hypothesis (Htr: tr <> Node nil).

  Let topo: DTree := fst (tree2Topo tr 0).
  Let cifc: CIfc := snd (tree2Topo tr 0).
  Let impl: System := impl Htr.

  Lemma mesi_InvWBCoh_init:
    Invariant.InvInit impl InvWBCoh.
  Proof.
    do 2 (red; simpl).
    intros.
    destruct (implOStatesInit tr)@[oidx] as [orq|] eqn:Host; simpl; auto.
    destruct (in_dec idx_dec oidx (c_li_indices cifc ++ c_l1_indices cifc)).
    - subst cifc; rewrite c_li_indices_head_rootOf in i by assumption.
      inv i.
      + rewrite implOStatesInit_value_root in Host by assumption.
        inv Host.
        red; intros.
        do 2 (red in H); dest_in.
      + rewrite implOStatesInit_value_non_root in Host by assumption.
        inv Host.
        red; intros.
        do 2 (red in H0); dest_in.
    - rewrite implOStatesInit_None in Host by assumption.
      discriminate.
  Qed.

  Lemma mesi_InvWBCoh_ext_in:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall eins,
        ValidMsgsExtIn impl eins ->
        InvWBCoh {| bst_oss := oss; bst_orqs := orqs; bst_msgs := enqMsgs eins msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H oidx); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    red; intros.
    apply InMP_enqMsgs_or in H2.
    destruct H2; [|eapply H; eauto].
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

  Lemma mesi_InvWBCoh_ext_out:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      InObjInds tr 0 {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
      forall (eouts: list (Id Msg)),
        InvWBCoh {| bst_oss := oss;
                    bst_orqs := orqs;
                    bst_msgs := deqMsgs (idsOf eouts) msgs |}.
  Proof.
    red; simpl; intros.
    specialize (H oidx); simpl in H.
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    red; intros; apply InMP_deqMsgs in H1; auto.
  Qed.

  Lemma InvWBCoh_no_update:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall oidx (post nost: OState),
        oss@[oidx] = Some post ->
        nost#[val] = post#[val] ->
        nost#[owned] = post#[owned] ->
        nost#[status] = post#[status] ->
        nost#[dir].(dir_st) = post#[dir].(dir_st) ->
        InvWBCoh {| bst_oss:= oss +[oidx <- nost];
                    bst_orqs:= orqs; bst_msgs:= msgs |}.
  Proof.
    unfold InvWBCoh; simpl; intros.
    mred; simpl; auto.
    specialize (H oidx).
    rewrite H0 in H; simpl in H.
    red; intros.
    specialize (H _ H5 H6).
    unfold ObjOwned in *; simpl in *; dest.
    rewrite H1.
    apply H.
    split.
    - rewrite <-H3; assumption.
    - rewrite <-H2; assumption.
  Qed.

  Lemma InvWBCoh_update_status_NoRqI:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall oidx (ost: OState),
        NoRqI oidx msgs ->
        InvWBCoh {| bst_oss:= oss +[oidx <- ost];
                    bst_orqs:= orqs; bst_msgs:= msgs |}.
  Proof.
    unfold InvWBCoh; simpl; intros.
    mred; simpl; auto.
    red; intros.
    specialize (H0 _ H1).
    red in H0; rewrite H2 in H0.
    unfold map in H0.
    rewrite caseDec_head_neq in H0 by discriminate.
    rewrite caseDec_head_eq in H0 by reflexivity.
    exfalso; auto.
  Qed.

  Lemma InvWBCoh_enqMP_valid:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall oidx ost midx msg,
        oss@[oidx] = Some ost ->
        midx = rqUpFrom oidx ->
        msg.(msg_id) = mesiInvWRq ->
        msg.(msg_value) = ost#[val] ->
        InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs;
                    bst_msgs:= enqMP midx msg msgs |}.
  Proof.
    unfold InvWBCoh; simpl; intros.
    destruct (idx_dec oidx0 oidx); subst.
    - specialize (H oidx).
      rewrite H0 in *; simpl in *.
      red; intros.
      apply InMP_enqMP_or in H1; destruct H1.
      + dest; simpl in *.
        intros; inv H4; assumption.
      + apply H; auto.
    - specialize (H oidx0).
      destruct (oss@[oidx0]) as [ost0|]; simpl in *; auto.
      red; intros.
      apply InMP_enqMP_or in H1; destruct H1.
      + exfalso; dest; subst.
        inv H4; rewrite H1 in H7; inv H7; auto.
      + apply H; auto.
  Qed.

  Lemma InvWBCoh_other_msg_id_enqMP:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx msg,
        msg.(msg_id) <> mesiInvWRq ->
        InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs;
                    bst_msgs:= enqMP midx msg msgs |}.
  Proof.
    unfold InvWBCoh; simpl; intros.
    specialize (H oidx).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    red; intros.
    apply InMP_enqMP_or in H1; destruct H1; auto.
    dest; subst.
    destruct idm as [midx msg]; simpl in *.
    inv H2; exfalso; auto.
  Qed.
  
  Lemma InvWBCoh_other_msg_id_enqMsgs:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall nmsgs,
        Forall (fun idm => (valOf idm).(msg_id) <> mesiInvWRq) nmsgs ->
        InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs;
                    bst_msgs:= enqMsgs nmsgs msgs |}.
  Proof.
    intros.
    generalize dependent msgs.
    induction nmsgs as [|[nmidx nmsg] nmsgs]; simpl; intros; auto.
    inv H0; dest.
    apply IHnmsgs; auto.
    apply InvWBCoh_other_msg_id_enqMP; assumption.
  Qed.

  Lemma InvWBCoh_deqMP:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall midx,
        InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs;
                    bst_msgs:= deqMP midx msgs |}.
  Proof.
    unfold InvWBCoh; simpl; intros.
    specialize (H oidx).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    red; intros; apply InMP_deqMP in H0; auto.
  Qed.

  Lemma InvWBCoh_deqMsgs:
    forall oss orqs msgs,
      InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs; bst_msgs:= msgs |} ->
      forall minds,
        InvWBCoh {| bst_oss:= oss; bst_orqs:= orqs;
                    bst_msgs:= deqMsgs minds msgs |}.
  Proof.
    unfold InvWBCoh; simpl; intros.
    specialize (H oidx).
    destruct (oss@[oidx]) as [ost|] eqn:Host; simpl in *; auto.
    red; intros; apply InMP_deqMsgs in H0; auto.
  Qed.

  Ltac simpl_InvWBCoh_enqMP :=
    simpl;
    try match goal with
        | [H: msg_id ?rmsg = _ |- msg_id ?rmsg <> _] => rewrite H
        end;
    discriminate.

  Ltac simpl_InvWBCoh_enqMsgs :=
    let idm := fresh "idm" in
    let Hin := fresh "H" in
    apply Forall_forall; intros idm Hin;
    apply in_map_iff in Hin; dest; subst;
    simpl_InvWBCoh_enqMP.

  Ltac simpl_InvWBCoh :=
    repeat
      (first [apply InvWBCoh_other_msg_id_enqMP; [|simpl_InvWBCoh_enqMP..]
             |apply InvWBCoh_other_msg_id_enqMsgs; [|simpl_InvWBCoh_enqMsgs]
             |apply InvWBCoh_deqMP
             |apply InvWBCoh_deqMsgs
             |apply InvWBCoh_update_status_NoRqI; [|assumption]
             |eapply InvWBCoh_no_update; [|eauto; fail..]
             |assumption]).

  Ltac solve_InvWBCoh :=
    let oidx := fresh "oidx" in
    red; simpl; intros oidx;
    match goal with
    | [Hi: InvWBCoh _ |- _] =>
      specialize (Hi oidx); simpl in Hi
    end;
    mred; simpl;
    let Hin := fresh "H" in
    let Hsig := fresh "H" in
    red; intros ? Hin Hsig;
    repeat 
      match goal with
      | [Hc: CohInvRq _ _ _ |- _] => specialize (Hc _ Hin Hsig); dest
      | [Hi: ObjInvWRq _ _ \/ ObjInvRq _ _ -> _ |- _] =>
        specialize (Hi (or_introl (@ex_intro _ _ _ (conj Hin Hsig))))
      end;
    simpl in *;
    solve [exfalso; solve_mesi|
           (* this is so arbitrary, but it works for all the remains *)
           unfold ObjOwned; simpl; intros; dest; discriminate].

  Lemma mesi_InvWBCoh_step:
    Invariant.InvStep impl step_m InvWBCoh.
  Proof.
    red; intros.
    pose proof (footprints_ok
                  (mesi_GoodORqsInit Htr)
                  (mesi_GoodRqRsSys Htr) H) as Hftinv.
    pose proof (mesi_InObjInds H) as Hioi.
    pose proof (mesi_MsgConflictsInv
                  (@mesi_RootChnInv_ok _ Htr) H) as Hpmcf.
    pose proof (MesiDownLockInv_ok H) as Hmdl.
    pose proof (mesi_InvWBDir_ok H) as Hidir.
    inv H1; [assumption
            |apply mesi_InvWBCoh_ext_in; auto
            |apply mesi_InvWBCoh_ext_out; auto
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

        all: try (simpl_InvWBCoh; fail).
        all: try (assert (NoRqI oidx msgs)
                   by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx);
                  simpl_InvWBCoh).
      }

      dest_in.
      { disc_rule_conds_ex.
        derive_MesiDownLockInv oidx.
        derive_InvWBDir oidx.
        simpl_InvWBCoh.
        solve_InvWBCoh.
      }
      { disc_rule_conds_ex.
        derive_MesiDownLockInv oidx.
        simpl_InvWBCoh; solve_InvWBCoh.
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

        all: try (simpl_InvWBCoh; fail).
        all: try (assert (NoRqI oidx msgs)
                   by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx);
                  simpl_InvWBCoh).
      }

      dest_in; disc_rule_conds_ex.

      all: try (simpl_InvWBCoh; fail).
      all: try (assert (NoRqI oidx msgs)
                 by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx);
                simpl_InvWBCoh).
      all: try (derive_footprint_info_basis oidx;
                assert (NoRqI oidx msgs)
                  by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx);
                simpl_InvWBCoh).
      all: try (simpl_InvWBCoh; solve_InvWBCoh; fail).
      all: try (derive_MesiDownLockInv oidx;
                derive_InvWBDir oidx;
                simpl_InvWBCoh; solve_InvWBCoh; fail).
      { eapply InvWBCoh_enqMP_valid; eauto. }

    - (*! Cases for L1 caches *)

      (** Derive some necessary information: each Li has a parent. *)
      apply in_map_iff in H1; destruct H1 as [oidx [? ?]]; subst.

      pose proof (tree2Topo_TreeTopoNode tr 0) as Htn.
      pose proof (c_l1_indices_has_parent Htr _ _ H2).
      destruct H1 as [pidx [? ?]].
      pose proof (Htn _ _ H4); dest.

      (** Do case analysis per a rule. *)
      dest_in; disc_rule_conds_ex.

      all: try (simpl_InvWBCoh; fail).
      all: try (assert (NoRqI oidx msgs)
                 by (solve_NoRqI_base; solve_NoRqI_by_no_locks oidx);
                simpl_InvWBCoh).
      all: try (derive_footprint_info_basis oidx;
                assert (NoRqI oidx msgs)
                  by (solve_NoRqI_base; solve_NoRqI_by_rsDown oidx);
                simpl_InvWBCoh).
      all: try (simpl_InvWBCoh; solve_InvWBCoh; fail).
      { eapply InvWBCoh_enqMP_valid; eauto. }

  Qed.

  Theorem mesi_InvWBCoh_ok:
    InvReachable impl step_m InvWBCoh.
  Proof.
    apply inv_reachable.
    - apply mesi_InvWBCoh_init.
    - apply mesi_InvWBCoh_step.
  Qed.

End InvWBCoh.

