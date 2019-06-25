Require Import Bool List String Peano_dec Lia.
Require Import Common FMap HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Msi MsiSv SpecSv MsiSvTopo.
Require Export MsiSvInvB.

Set Implicit Arguments.

Import MonadNotations.
Import CaseNotations.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

(* NOTE: these ltacs only work for constants (channels, objects, etc.),
 * thus will be used only in this file.
 *)
Ltac get_lock_minds oidx :=
  progress (good_footprint_get oidx);
  repeat disc_footprints_ok;
  disc_minds_const.

Ltac get_lock_inv obj sys :=
  let H := fresh "H" in
  assert (In obj (sys_objs sys)) as H by (simpl; tauto);
  progress (good_locking_get obj);
  clear H.

Ltac exfalso_uplock_rq_rs upidx urqUp udown :=
  progress
    match goal with
    | [H: UpLockInvORq _ _ _ _ _ |- _] =>
      eapply upLockInvORq_rqUp_down_rssQ_False
        with (pidx:= upidx) (rqUp:= urqUp) (down:= udown) in H;
      try reflexivity; auto
    end;
  repeat
    match goal with
    | [ |- Datatypes.length (findQ _ _) >= 1] =>
      eapply findQ_length_ge_one; eassumption
    | [ |- Datatypes.length (rssQ _ _) >= 1] =>
      eapply rssQ_length_ge_one; [|eassumption]; eassumption
    | [H: FirstMPI _ (?midx, _) |- InMP ?midx _ _] =>
      apply FirstMP_InMP; eassumption
    end.

Ltac exfalso_uplock_rq_two upidx urqUp m1 m2 :=
  progress
    match goal with
    | [H: UpLockInvORq _ _ _ _ _ |- _] =>
      eapply upLockInvORq_rqUp_length_two_False
        with (pidx:= upidx) (rqUp:= urqUp) in H;
      try reflexivity; auto
    end;
  repeat
    match goal with
    | [ |- Datatypes.length (findQ _ _) >= 2] =>
      eapply findQ_length_two with (msg1:= m1) (msg2:= m2);
      try eassumption; auto
    | [ |- _ <> _] => intro Hx; subst; simpl in *; discriminate
    end.

Ltac exfalso_uplock_rs_two upidx udown m1 m2 :=
  progress
    match goal with
    | [H: UpLockInvORq _ _ _ _ _ |- _] =>
      eapply upLockInvORq_down_rssQ_length_two_False
        with (pidx:= upidx) (down:= udown) in H;
      try reflexivity; auto
    end;
  repeat
    match goal with
    | [ |- Datatypes.length (rssQ _ _) >= 2] =>
      eapply rssQ_length_two with (msg1:= m1) (msg2:= m2);
      try eassumption; auto
    | [ |- _ <> _] => intro Hx; subst; simpl in *; discriminate
    | [ |- InMP ?midx ?msg (enqMP ?midx ?msg _)] =>
      apply InMP_or_enqMP; left; auto; fail
    | [ |- InMP _ _ (enqMP _ _ _)] =>
      apply InMP_or_enqMP; right
    | [ |- InMP _ _ (deqMP _ _)] =>
      eapply deqMP_InMP; try eassumption
    end.

Section Inv.

  Definition ImplOStateMSI (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    msiS <= ost#[implStatusIdx] -> ost#[implValueIdx] = cv.

  Definition MsgExistsSig (sig: MSig) (msgs: MessagePool Msg) :=
    exists idm, InMPI msgs idm /\ sigOf idm = sig.

  Section InvExcl.
    Variables (dir: MSI)
              (porq: ORq Msg)
              (cost: OState ImplOStateIfc)
              (corq: ORq Msg)
              (pc cpRq cpRs: IdxT)
              (msgs: MessagePool Msg).

    Definition InvalidMsg (idm: Id Msg) :=
      match case (sigOf idm) on sig_dec default True with
      | (pc, (MRs, msiRsS)): False
      | (cpRs, (MRs, msiDownRsS)): False
      | (cpRq, (MRq, msiRqI)): cost#[implStatusIdx] = msiI
      end.
    
    Definition InvalidMsgs :=
      forall idm,
        InMPI msgs idm ->
        match case (sigOf idm) on sig_dec default True with
        | (pc, (MRs, msiRsS)): False
        | (cpRs, (MRs, msiDownRsS)): False
        | (cpRq, (MRq, msiRqI)): cost#[implStatusIdx] = msiI
        end.

    (** Required when handling [setRq], need to know [DirMsgsCoh] but instead
     * [InvalidMsgs] holds and it implies [DirMsgsCoh].
     *)
    Definition ChildExcl :=
      msiM <= cost#[implStatusIdx] -> corq@[upRq] = None ->
      InvalidMsgs.

    Definition DirExcl :=
      msiM <= dir ->
      porq@[downRq] = None ->
      MsgExistsSig (cpRq, (MRq, msiRqI)) msgs ->
      msiM <= cost#[implStatusIdx].

    Definition ExclInv :=
      ChildExcl /\ DirExcl.

  End InvExcl.

  Section InvInvalid.
    Variables (dir: MSI)
              (cost: OState ImplOStateIfc)
              (pc cpRq cpRs: IdxT)
              (msgs: MessagePool Msg).

    Definition ChildInvalid :=
      cost#[implStatusIdx] = msiI \/
      MsgExistsSig (pc, (MRs, msiRsI)) msgs.
    
    Definition InvalidInv :=
      dir = msiI ->
      ChildInvalid /\ InvalidMsgs cost pc cpRq cpRs msgs.

  End InvInvalid.

  Section InvDir.
    Variables (post cost1 cost2: OState ImplOStateIfc)
              (porq corq1 corq2: ORq Msg).

    (* Why soundness of the directory:
     * 1) We need to relax when an object value is coherent, by allowing
     *    the case where [Ci.st >= S /\ P.dir.Ci >= S] and [Ci] not necessarily
     *    being lock-free.
     * 2) In order to know an object value is coherent when [Ci.st >= S] and
     *    [Ci] is lock-free, we need this soundness.
     *)
    Definition DirSound1: Prop :=
      !corq1@[upRq]; cost1#[implStatusIdx] <= post#[implDirIdx].(fst).

    Definition DirSound2: Prop :=
      !corq2@[upRq]; cost2#[implStatusIdx] <= post#[implDirIdx].(snd).

    Definition DirComplete1: Prop :=
      !corq1@[upRq]; !porq@[downRq];
        post#[implDirIdx].(fst) <= cost1#[implStatusIdx].

    Definition DirComplete2: Prop :=
      !corq2@[upRq]; !porq@[downRq];
        post#[implDirIdx].(snd) <= cost2#[implStatusIdx].

    Definition DirInv: Prop :=
      DirSound1 /\ DirSound2 /\
      DirComplete1 /\ DirComplete2.

  End InvDir.

  Definition ImplInv (st: MState ImplOStateIfc): Prop :=
    post <-- (bst_oss st)@[parentIdx];
      cost1 <-- (bst_oss st)@[child1Idx];
      cost2 <-- (bst_oss st)@[child2Idx];
      porq <-- (bst_orqs st)@[parentIdx];
      corq1 <-- (bst_orqs st)@[child1Idx];
      corq2 <-- (bst_orqs st)@[child2Idx];
      DirInv post cost1 cost2 porq corq1 corq2 /\
      ExclInv (fst post#[implDirIdx]) porq cost1 corq1
              pc1 c1pRq c1pRs (bst_msgs st) /\
      ExclInv (snd post#[implDirIdx]) porq cost2 corq2
              pc2 c2pRq c2pRs (bst_msgs st) /\
      InvalidInv post#[implDirIdx].(fst) cost1 pc1 c1pRq c1pRs (bst_msgs st) /\
      InvalidInv post#[implDirIdx].(snd) cost2 pc2 c2pRq c2pRs (bst_msgs st).

  Hint Unfold ImplOStateMSI ChildExcl DirExcl ExclInv InvalidInv
       DirSound1 DirSound2 DirComplete1 DirComplete2 DirInv: RuleConds.

  Section Facts.

    Lemma dirInv_orqs_weakened_p:
      forall post cost1 cost2 porq corq1 corq2,
        DirInv post cost1 cost2 porq corq1 corq2 ->
        forall rty rqi,
          DirInv post cost1 cost2 (porq +[rty <- rqi]) corq1 corq2.
    Proof.
      unfold DirInv; intros; dest.
      repeat split; try assumption.
      - red in H1; red; mred.
      - red in H2; red; mred.
    Qed.

    Lemma dirInv_orqs_weakened_1:
      forall post cost1 cost2 porq corq1 corq2,
        DirInv post cost1 cost2 porq corq1 corq2 ->
        forall rty rqi,
          DirInv post cost1 cost2 porq (corq1 +[rty <- rqi]) corq2.
    Proof.
      unfold DirInv; intros; dest.
      repeat split; try assumption.
      - red in H; red; mred.
      - red in H1; red; mred.
    Qed.

    Lemma dirInv_orqs_weakened_2:
      forall post cost1 cost2 porq corq1 corq2,
        DirInv post cost1 cost2 porq corq1 corq2 ->
        forall rty rqi,
          DirInv post cost1 cost2 porq corq1 (corq2 +[rty <- rqi]).
    Proof.
      unfold DirInv; intros; dest.
      repeat split; try assumption.
      - red in H0; red; mred.
      - red in H2; red; mred.
    Qed.

    Lemma exclInv_parent_orqs_weakened:
      forall dir porq cost corq pc cpRq cpRs msgs,
        ExclInv dir porq cost corq pc cpRq cpRs msgs ->
        forall rty rqi,
          ExclInv dir (porq +[rty <- rqi]) cost corq pc cpRq cpRs msgs.
    Proof.
      unfold ExclInv; intros; dest.
      split; [assumption|].
      red in H0; red; mred.
    Qed.

    Lemma exclInv_child_orqs_weakened:
      forall dir porq cost corq pc cpRq cpRs msgs,
        ExclInv dir porq cost corq pc cpRq cpRs msgs ->
        forall rty rqi,
          ExclInv dir porq cost (corq +[rty <- rqi]) pc cpRq cpRs msgs.
    Proof.
      unfold ExclInv; intros; dest.
      split; [|assumption].
      red in H; red; mred.
    Qed.

    Lemma implInv_orqs_weakened:
      forall oss orqs msgs,
        ImplInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
        forall oidx porq norq rty rqi,
          orqs@[oidx] = Some porq ->
          norq = porq +[rty <- rqi] ->
          ImplInv {| bst_oss := oss;
                     bst_orqs := orqs +[oidx <- norq];
                     bst_msgs := msgs |}.
    Proof.
      unfold ImplInv; simpl; intros.
      disc_rule_conds_const; dest.
      mred; simpl; auto.
      - repeat ssplit; try assumption.
        + apply dirInv_orqs_weakened_p; assumption.
        + apply exclInv_parent_orqs_weakened; assumption.
        + apply exclInv_parent_orqs_weakened; assumption.
      - repeat ssplit; try assumption.
        + apply dirInv_orqs_weakened_1; assumption.
        + apply exclInv_child_orqs_weakened; assumption.
      - repeat ssplit; try assumption.
        + apply dirInv_orqs_weakened_2; assumption.
        + apply exclInv_child_orqs_weakened; assumption.
    Qed.

    Lemma msgExistsSig_enqMP:
      forall sig msgs,
        MsgExistsSig sig msgs ->
        forall nmidx nmsg,
          MsgExistsSig sig (enqMP nmidx nmsg msgs).
    Proof.
      unfold MsgExistsSig; intros.
      destruct H as [[midx msg] [? ?]]; subst.
      exists (midx, msg); split; auto.
      apply InMP_or_enqMP; auto.
    Qed.

    Lemma msgExistsSig_enqMsgs:
      forall sig msgs,
        MsgExistsSig sig msgs ->
        forall nmsgs,
          MsgExistsSig sig (enqMsgs nmsgs msgs).
    Proof.
      unfold MsgExistsSig; intros.
      destruct H as [[midx msg] [? ?]]; subst.
      exists (midx, msg); split; auto.
      apply InMP_or_enqMsgs; auto.
    Qed.

    Lemma msgExistsSig_deqMP:
      forall sig msgs,
        MsgExistsSig sig msgs ->
        forall rmidx,
          rmidx <> fst sig ->
          MsgExistsSig sig (deqMP rmidx msgs).
    Proof.
      unfold MsgExistsSig; intros.
      destruct H as [[midx msg] [? ?]]; subst.
      exists (midx, msg); split; auto.
      apply deqMP_InMP_midx; auto.
    Qed.

    Lemma msgExistsSig_deqMsgs:
      forall sig msgs,
        MsgExistsSig sig msgs ->
        forall rminds,
          ~ In (fst sig) rminds ->
          MsgExistsSig sig (deqMsgs rminds msgs).
    Proof.
      unfold MsgExistsSig; intros.
      destruct H as [[midx msg] [? ?]]; subst.
      exists (midx, msg); split; auto.
      apply deqMsgs_InMP_midx; auto.
    Qed.

    Lemma msgExistsSig_enqMP_or:
      forall sig msgs nmidx nmsg,
        MsgExistsSig sig (enqMP nmidx nmsg msgs) ->
        sigOf (nmidx, nmsg) = sig \/ MsgExistsSig sig msgs.
    Proof.
      unfold MsgExistsSig; intros.
      destruct H as [[midx msg] [? ?]]; subst.
      apply InMP_enqMP_or in H; destruct H; eauto.
      simpl in *; dest; subst; auto.
    Qed.

    Lemma msgExistsSig_enqMsgs_or:
      forall sig msgs nmsgs,
        MsgExistsSig sig (enqMsgs nmsgs msgs) ->
        (exists idm, In idm nmsgs /\ sigOf idm = sig) \/
        MsgExistsSig sig msgs.
    Proof.
      unfold MsgExistsSig; intros.
      destruct H as [[midx msg] [? ?]]; subst.
      apply InMP_enqMsgs_or in H; destruct H; eauto.
    Qed.

    Lemma msgExistsSig_deqMP_inv:
      forall sig msgs rmidx,
        MsgExistsSig sig (deqMP rmidx msgs) ->
        MsgExistsSig sig msgs.
    Proof.
      unfold MsgExistsSig; intros.
      destruct H as [[midx msg] [? ?]]; subst.
      apply InMP_deqMP in H.
      eauto.
    Qed.

    Lemma msgExistsSig_deqMsgs_inv:
      forall sig msgs rminds,
        MsgExistsSig sig (deqMsgs rminds msgs) ->
        MsgExistsSig sig msgs.
    Proof.
      unfold MsgExistsSig; intros.
      destruct H as [[midx msg] [? ?]]; subst.
      apply InMP_deqMsgs in H.
      eauto.
    Qed.

    Lemma childInvalid_enqMP:
      forall cost pc msgs,
        ChildInvalid cost pc msgs ->
        forall midx msg,
          ChildInvalid cost pc (enqMP midx msg msgs).
    Proof.
      unfold ChildInvalid; intros.
      destruct H; [left; auto|right].
      apply msgExistsSig_enqMP; assumption.
    Qed.

    Lemma childInvalid_enqMsgs:
      forall cost pc msgs,
        ChildInvalid cost pc msgs ->
        forall nmsgs,
          ChildInvalid cost pc (enqMsgs nmsgs msgs).
    Proof.
      unfold ChildInvalid; intros.
      destruct H; [left; auto|right].
      apply msgExistsSig_enqMsgs; assumption.
    Qed.

    Lemma childInvalid_other_midx_deqMP:
      forall cost pc msgs,
        ChildInvalid cost pc msgs ->
        forall midx,
          midx <> pc ->
          ChildInvalid cost pc (deqMP midx msgs).
    Proof.
      unfold ChildInvalid; intros.
      destruct H; [left; auto|right].
      apply msgExistsSig_deqMP; auto.
    Qed.

    Lemma childInvalid_other_midx_deqMsgs:
      forall cost pc msgs,
        ChildInvalid cost pc msgs ->
        forall rminds,
          ~ In pc rminds ->
          ChildInvalid cost pc (deqMsgs rminds msgs).
    Proof.
      unfold ChildInvalid; intros.
      destruct H; [left; auto|right].
      apply msgExistsSig_deqMsgs; auto.
    Qed.

    Lemma invalidMsgs_other_midx_enqMP:
      forall cost pc cpRq cpRs msgs,
        InvalidMsgs cost pc cpRq cpRs msgs ->
        forall midx msg,
          ~ In midx [pc; cpRq; cpRs] ->
          InvalidMsgs cost pc cpRq cpRs (enqMP midx msg msgs).
    Proof.
      unfold InvalidMsgs; intros.
      apply InMP_enqMP_or in H1; destruct H1; dest; subst.
      - destruct idm as [midx msg]; simpl in H0.
        unfold caseDec.
        repeat (destruct (sig_dec _ _); try (exfalso; inv e; auto)).
        auto.
      - specialize (H _ H1).
        unfold caseDec in *.
        repeat (destruct (sig_dec _ _); [exfalso; auto; fail|]).
        destruct (sig_dec _ _); auto.
    Qed.

    Lemma invalidMsgs_other_midx_enqMsgs:
      forall cost pc cpRq cpRs msgs,
        InvalidMsgs cost pc cpRq cpRs msgs ->
        forall nmsgs,
          DisjList (idsOf nmsgs) [pc; cpRq; cpRs] ->
          InvalidMsgs cost pc cpRq cpRs (enqMsgs nmsgs msgs).
    Proof.
      unfold InvalidMsgs; intros.
      apply InMP_enqMsgs_or in H1; destruct H1; dest; subst.
      - destruct idm as [midx msg]; simpl in H1.
        unfold caseDec.
        repeat (destruct (sig_dec _ _);
                [exfalso; inv e;
                 apply in_map with (f:= idOf) in H1;
                 eapply DisjList_In_1; eauto; simpl; tauto|]).
        auto.
      - specialize (H _ H1).
        unfold caseDec in *.
        repeat (destruct (sig_dec _ _); [exfalso; auto; fail|]).
        destruct (sig_dec _ _); auto.
    Qed.

    Lemma invalidMsgs_other_msg_id_enqMP:
      forall cost pc cpRq cpRs msgs,
        InvalidMsgs cost pc cpRq cpRs msgs ->
        forall midx msg,
          ~ In msg.(msg_id) [msiRsS; msiDownRsS; msiRqI] ->
          InvalidMsgs cost pc cpRq cpRs (enqMP midx msg msgs).
    Proof.
      unfold InvalidMsgs; intros.
      apply InMP_enqMP_or in H1; destruct H1; dest; subst.
      - destruct idm as [midx msg]; simpl in H0.
        unfold caseDec.
        repeat (destruct (sig_dec _ _); try (exfalso; inv e; auto)).
        auto.
      - specialize (H _ H1).
        unfold caseDec in *.
        repeat (destruct (sig_dec _ _); [exfalso; auto; fail|]).
        destruct (sig_dec _ _); auto.
    Qed.

    Lemma invalidMsgs_other_msg_id_enqMsgs:
      forall cost pc cpRq cpRs msgs,
        InvalidMsgs cost pc cpRq cpRs msgs ->
        forall nmsgs,
          DisjList (map (fun idm => (valOf idm).(msg_id)) nmsgs)
                   [msiRsS; msiDownRsS; msiRqI] ->
          InvalidMsgs cost pc cpRq cpRs (enqMsgs nmsgs msgs).
    Proof.
      unfold InvalidMsgs; intros.
      apply InMP_enqMsgs_or in H1; destruct H1; dest; subst.
      - destruct idm as [midx msg]; simpl in H1.
        unfold caseDec.
        repeat (destruct (sig_dec _ _);
                [exfalso; inv e;
                 apply in_map with (f:= fun idm => (valOf idm).(msg_id)) in H1;
                 eapply DisjList_In_1; eauto;
                 simpl; rewrite H5; tauto|]).
        auto.
      - specialize (H _ H1).
        unfold caseDec in *.
        repeat (destruct (sig_dec _ _); [exfalso; auto; fail|]).
        destruct (sig_dec _ _); auto.
    Qed.

    Lemma invalidMsgs_deqMP:
      forall cost pc cpRq cpRs msgs,
        InvalidMsgs cost pc cpRq cpRs msgs ->
        forall rmidx,
          InvalidMsgs cost pc cpRq cpRs (deqMP rmidx msgs).
    Proof.
      unfold InvalidMsgs; intros.
      apply InMP_deqMP in H0.
      destruct idm as [midx msg]; simpl in H0.
      specialize (H (midx, msg) H0).
      unfold caseDec in *.
      repeat (destruct (sig_dec _ _); [exfalso; auto; fail|]).
      destruct (sig_dec _ _); auto.
    Qed.

    Lemma invalidMsgs_deqMsgs:
      forall cost pc cpRq cpRs msgs,
        InvalidMsgs cost pc cpRq cpRs msgs ->
        forall rminds,
          InvalidMsgs cost pc cpRq cpRs (deqMsgs rminds msgs).
    Proof.
      unfold InvalidMsgs; intros.
      apply InMP_deqMsgs in H0.
      specialize (H _ H0).
      unfold caseDec in *.
      repeat (destruct (sig_dec _ _); [exfalso; auto; fail|]).
      destruct (sig_dec _ _); auto.
    Qed.

    Lemma invalidMsgs_enqMP:
      forall cost pc cpRq cpRs msgs,
        InvalidMsgs cost pc cpRq cpRs msgs ->
        forall midx msg,
          InvalidMsg cost pc cpRq cpRs (midx, msg) ->
          InvalidMsgs cost pc cpRq cpRs (enqMP midx msg msgs).
    Proof.
      unfold InvalidMsgs, InvalidMsg; intros.
      apply InMP_enqMP_or in H1; destruct H1; [dest|auto].
      destruct idm as [midx' msg']; simpl in H1, H2; subst.
      assumption.
    Qed.
    
    Lemma exclInv_other_midx_enqMP:
      forall dir porq cost corq pc cpRq cpRs msgs,
        ExclInv dir porq cost corq pc cpRq cpRs msgs ->
        forall midx msg,
          ~ In midx [pc; cpRq; cpRs] ->
          ExclInv dir porq cost corq pc cpRq cpRs (enqMP midx msg msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split; intros.
      - apply invalidMsgs_other_midx_enqMP; auto.
      - apply H1; auto.
        apply msgExistsSig_enqMP_or in H4.
        destruct H4; auto.
        inv H4; exfalso; auto.
    Qed.

    Lemma exclInv_other_midx_enqMsgs:
      forall dir porq cost corq pc cpRq cpRs msgs,
        ExclInv dir porq cost corq pc cpRq cpRs msgs ->
        forall nmsgs,
          DisjList (idsOf nmsgs) [pc; cpRq; cpRs] ->
          ExclInv dir porq cost corq pc cpRq cpRs (enqMsgs nmsgs msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split; intros.
      - apply invalidMsgs_other_midx_enqMsgs; auto.
      - apply H1; auto.
        apply msgExistsSig_enqMsgs_or in H4.
        destruct H4; auto.
        destruct H4 as [[midx msg] [? ?]].
        inv H5.
        apply in_map with (f:= idOf) in H4.
        exfalso; eapply DisjList_In_1; eauto.
        simpl; tauto.
    Qed.

    Lemma exclInv_other_msg_id_enqMP:
      forall dir porq cost corq pc cpRq cpRs msgs,
        ExclInv dir porq cost corq pc cpRq cpRs msgs ->
        forall midx msg,
          ~ In msg.(msg_id) [msiRsS; msiDownRsS; msiRqI] ->
          ExclInv dir porq cost corq pc cpRq cpRs (enqMP midx msg msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split; intros.
      - apply invalidMsgs_other_msg_id_enqMP; auto.
      - apply H1; auto.
        apply msgExistsSig_enqMP_or in H4.
        destruct H4; auto.
        inv H4; exfalso; auto.
    Qed.

    Lemma exclInv_other_msg_id_enqMsgs:
      forall dir porq cost corq pc cpRq cpRs msgs,
        ExclInv dir porq cost corq pc cpRq cpRs msgs ->
        forall nmsgs,
          DisjList (map (fun idm => (valOf idm).(msg_id)) nmsgs)
                   [msiRsS; msiDownRsS; msiRqI] ->
          ExclInv dir porq cost corq pc cpRq cpRs (enqMsgs nmsgs msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split; intros.
      - apply invalidMsgs_other_msg_id_enqMsgs; auto.
      - apply H1; auto.
        apply msgExistsSig_enqMsgs_or in H4.
        destruct H4; auto.
        destruct H4 as [[midx msg] [? ?]].
        inv H5.
        apply in_map with (f:= fun idm => (valOf idm).(msg_id)) in H4.
        simpl in H4; rewrite H9 in H4.
        exfalso; eapply DisjList_In_1; eauto.
        simpl; tauto.
    Qed.

    Lemma exclInv_other_midx_deqMP:
      forall dir porq cost corq pc cpRq cpRs msgs,
        ExclInv dir porq cost corq pc cpRq cpRs msgs ->
        forall rmidx,
          ~ In rmidx [pc; cpRq; cpRs] ->
          ExclInv dir porq cost corq pc cpRq cpRs (deqMP rmidx msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split; intros.
      - apply invalidMsgs_deqMP; auto.
      - apply H1; auto.
        apply msgExistsSig_deqMP_inv in H4; auto.
    Qed.

    Lemma exclInv_other_midx_deqMsgs:
      forall dir porq cost corq pc cpRq cpRs msgs,
        ExclInv dir porq cost corq pc cpRq cpRs msgs ->
        forall rminds,
          DisjList rminds [pc; cpRq; cpRs] ->
          ExclInv dir porq cost corq pc cpRq cpRs (deqMsgs rminds msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split; intros.
      - apply invalidMsgs_deqMsgs; auto.
      - apply H1; auto.
        apply msgExistsSig_deqMsgs_inv in H4; auto.
    Qed.

    Lemma invalidInv_other_midx_enqMP:
      forall dir cost pc cpRq cpRs msgs,
        InvalidInv dir cost pc cpRq cpRs msgs ->
        forall midx msg,
          ~ In midx [pc; cpRq; cpRs] ->
          InvalidInv dir cost pc cpRq cpRs (enqMP midx msg msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split.
      - red in H; red.
        destruct H; [left; assumption|right].
        apply msgExistsSig_enqMP; auto.
      - apply invalidMsgs_other_midx_enqMP; auto.
    Qed.

    Lemma invalidInv_other_midx_enqMsgs:
      forall dir cost  pc cpRq cpRs msgs,
        InvalidInv dir cost pc cpRq cpRs msgs ->
        forall nmsgs,
          DisjList (idsOf nmsgs) [pc; cpRq; cpRs] ->
          InvalidInv dir cost pc cpRq cpRs (enqMsgs nmsgs msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split; intros.
      - red in H; red.
        destruct H; [left; assumption|right].
        apply msgExistsSig_enqMsgs; auto.
      - apply invalidMsgs_other_midx_enqMsgs; auto.
    Qed.

    Lemma invalidInv_other_msg_id_enqMP:
      forall dir cost pc cpRq cpRs msgs,
        InvalidInv dir cost pc cpRq cpRs msgs ->
        forall midx msg,
          ~ In msg.(msg_id) [msiRsS; msiDownRsS; msiRqI] ->
          InvalidInv dir cost pc cpRq cpRs (enqMP midx msg msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split.
      - red in H; red.
        destruct H; [left; assumption|right].
        apply msgExistsSig_enqMP; auto.
      - apply invalidMsgs_other_msg_id_enqMP; auto.
    Qed.

    Lemma invalidInv_other_msg_id_enqMsgs:
      forall dir cost  pc cpRq cpRs msgs,
        InvalidInv dir cost pc cpRq cpRs msgs ->
        forall nmsgs,
          DisjList (map (fun idm => (valOf idm).(msg_id)) nmsgs)
                   [msiRsS; msiDownRsS; msiRqI] ->
          InvalidInv dir cost pc cpRq cpRs (enqMsgs nmsgs msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split; intros.
      - red in H; red.
        destruct H; [left; assumption|right].
        apply msgExistsSig_enqMsgs; auto.
      - apply invalidMsgs_other_msg_id_enqMsgs; auto.
    Qed.

    Lemma invalidInv_other_midx_deqMP:
      forall dir cost pc cpRq cpRs msgs,
        InvalidInv dir cost pc cpRq cpRs msgs ->
        forall rmidx,
          ~ In rmidx [pc; cpRq; cpRs] ->
          InvalidInv dir cost pc cpRq cpRs (deqMP rmidx msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split.
      - red in H; red.
        destruct H; [left; assumption|right].
        apply msgExistsSig_deqMP; auto.
      - apply invalidMsgs_deqMP; auto.
    Qed.

    Lemma invalidInv_other_midx_deqMsgs:
      forall dir cost  pc cpRq cpRs msgs,
        InvalidInv dir cost pc cpRq cpRs msgs ->
        forall rminds,
          DisjList rminds [pc; cpRq; cpRs] ->
          InvalidInv dir cost pc cpRq cpRs (deqMsgs rminds msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split; intros.
      - red in H; red.
        destruct H; [left; assumption|right].
        apply msgExistsSig_deqMsgs; auto.
        eapply DisjList_In_1; eauto.
        simpl; tauto.
      - apply invalidMsgs_deqMsgs; auto.
    Qed.

    Lemma implInv_other_midx_enqMP:
      forall oss orqs msgs,
        ImplInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
        forall midx msg,
          ~ In midx [pc1; c1pRq; c1pRs; pc2; c2pRq; c2pRs] ->
          ImplInv {| bst_oss := oss;
                     bst_orqs := orqs;
                     bst_msgs := enqMP midx msg msgs |}.
    Proof.
      intros.
      red in H; red; simpl in *.
      disc_rule_conds_const; dest.
      repeat ssplit; [assumption|..].
      - apply exclInv_other_midx_enqMP; auto.
        intro Hx; elim H0; dest_in; tauto.
      - apply exclInv_other_midx_enqMP; auto.
        intro Hx; elim H0; dest_in; tauto.
      - apply invalidInv_other_midx_enqMP; auto.
        intro Hx; elim H0; dest_in; tauto.
      - apply invalidInv_other_midx_enqMP; auto.
        intro Hx; elim H0; dest_in; tauto.
    Qed.

    Lemma implInv_other_midx_enqMsgs:
      forall oss orqs msgs,
        ImplInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
        forall nmsgs,
          DisjList (idsOf nmsgs) [pc1; c1pRq; c1pRs; pc2; c2pRq; c2pRs] ->
          ImplInv {| bst_oss := oss;
                     bst_orqs := orqs;
                     bst_msgs := enqMsgs nmsgs msgs |}.
    Proof.
      intros.
      red in H; red; simpl in *.
      disc_rule_conds_const; dest.
      repeat ssplit; [assumption|..].
      - apply exclInv_other_midx_enqMsgs; auto.
        eapply DisjList_comm, DisjList_SubList;
          [|apply DisjList_comm; eassumption].
        solve_SubList.
      - apply exclInv_other_midx_enqMsgs; auto.
        eapply DisjList_comm, DisjList_SubList;
          [|apply DisjList_comm; eassumption].
        solve_SubList.
      - apply invalidInv_other_midx_enqMsgs; auto.
        eapply DisjList_comm, DisjList_SubList;
          [|apply DisjList_comm; eassumption].
        solve_SubList.
      - apply invalidInv_other_midx_enqMsgs; auto.
        eapply DisjList_comm, DisjList_SubList;
          [|apply DisjList_comm; eassumption].
        solve_SubList.
    Qed.

    Lemma implInv_other_msg_id_enqMP:
      forall oss orqs msgs,
        ImplInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
        forall midx msg,
          ~ In msg.(msg_id) [msiRsS; msiDownRsS; msiRqI] ->
          ImplInv {| bst_oss := oss;
                     bst_orqs := orqs;
                     bst_msgs := enqMP midx msg msgs |}.
    Proof.
      intros.
      red in H; red; simpl in *.
      disc_rule_conds_const; dest.
      repeat ssplit; [assumption|..].
      - apply exclInv_other_msg_id_enqMP; auto.
      - apply exclInv_other_msg_id_enqMP; auto.
      - apply invalidInv_other_msg_id_enqMP; auto.
      - apply invalidInv_other_msg_id_enqMP; auto.
    Qed.

    Lemma implInv_other_msg_id_enqMsgs:
      forall oss orqs msgs,
        ImplInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
        forall nmsgs,
          DisjList (map (fun idm => (valOf idm).(msg_id)) nmsgs)
                   [msiRsS; msiDownRsS; msiRqI] ->
          ImplInv {| bst_oss := oss;
                     bst_orqs := orqs;
                     bst_msgs := enqMsgs nmsgs msgs |}.
    Proof.
      intros.
      red in H; red; simpl in *.
      disc_rule_conds_const; dest.
      repeat ssplit; [assumption|..].
      - apply exclInv_other_msg_id_enqMsgs; auto.
      - apply exclInv_other_msg_id_enqMsgs; auto.
      - apply invalidInv_other_msg_id_enqMsgs; auto.
      - apply invalidInv_other_msg_id_enqMsgs; auto.
    Qed.
    
    Lemma implInv_other_midx_deqMP:
      forall oss orqs msgs,
        ImplInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
        forall rmidx,
          ~ In rmidx [pc1; c1pRq; c1pRs; pc2; c2pRq; c2pRs] ->
          ImplInv {| bst_oss := oss;
                     bst_orqs := orqs;
                     bst_msgs := deqMP rmidx msgs |}.
    Proof.
      intros.
      red in H; red; simpl in *.
      disc_rule_conds_const; dest.
      repeat ssplit; [assumption|..].
      - apply exclInv_other_midx_deqMP; auto.
        intro Hx; elim H0; dest_in; tauto.
      - apply exclInv_other_midx_deqMP; auto.
        intro Hx; elim H0; dest_in; tauto.
      - apply invalidInv_other_midx_deqMP; auto.
        intro Hx; elim H0; dest_in; tauto.
      - apply invalidInv_other_midx_deqMP; auto.
        intro Hx; elim H0; dest_in; tauto.
    Qed.

    Lemma implInv_other_midx_deqMsgs:
      forall oss orqs msgs,
        ImplInv {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} ->
        forall rminds,
          DisjList rminds [pc1; c1pRq; c1pRs; pc2; c2pRq; c2pRs] ->
          ImplInv {| bst_oss := oss;
                     bst_orqs := orqs;
                     bst_msgs := deqMsgs rminds msgs |}.
    Proof.
      intros.
      red in H; red; simpl in *.
      disc_rule_conds_const; dest.
      repeat ssplit; [assumption|..].
      - apply exclInv_other_midx_deqMsgs; auto.
        eapply DisjList_comm, DisjList_SubList;
          [|apply DisjList_comm; eassumption].
        solve_SubList.
      - apply exclInv_other_midx_deqMsgs; auto.
        eapply DisjList_comm, DisjList_SubList;
          [|apply DisjList_comm; eassumption].
        solve_SubList.
      - apply invalidInv_other_midx_deqMsgs; auto.
        eapply DisjList_comm, DisjList_SubList;
          [|apply DisjList_comm; eassumption].
        solve_SubList.
      - apply invalidInv_other_midx_deqMsgs; auto.
        eapply DisjList_comm, DisjList_SubList;
          [|apply DisjList_comm; eassumption].
        solve_SubList.
    Qed.

    Lemma msiSv_impl_InvTrs_ext_in:
      forall st1 eins st2,
        ImplInv st1 ->
        step_m impl st1 (RlblIns eins) st2 ->
        ImplInv st2.
    Proof.
      intros; inv_step.
      red in H; red; simpl in *.
      disc_rule_conds_const; dest.
      destruct H3.
      repeat ssplit; try assumption.

      - apply exclInv_other_midx_enqMsgs; auto.
        eapply DisjList_SubList; [eassumption|].
        solve_DisjList.
      - apply exclInv_other_midx_enqMsgs; auto.
        eapply DisjList_SubList; [eassumption|].
        solve_DisjList.
      - apply invalidInv_other_midx_enqMsgs; auto.
        eapply DisjList_SubList; [eassumption|].
        solve_DisjList.
      - apply invalidInv_other_midx_enqMsgs; auto.
        eapply DisjList_SubList; [eassumption|].
        solve_DisjList.
    Qed.

    Lemma msiSv_impl_InvTrs_ext_out:
      forall st1 eouts st2,
        ImplInv st1 ->
        step_m impl st1 (RlblOuts eouts) st2 ->
        ImplInv st2.
    Proof.
      intros; inv_step.
      red in H; red; simpl in *.
      disc_rule_conds_const; dest.
      destruct H4.
      repeat ssplit; try assumption.

      - apply exclInv_other_midx_deqMsgs; auto.
        eapply DisjList_SubList; [eassumption|].
        solve_DisjList.
      - apply exclInv_other_midx_deqMsgs; auto.
        eapply DisjList_SubList; [eassumption|].
        solve_DisjList.
      - apply invalidInv_other_midx_deqMsgs; auto.
        eapply DisjList_SubList; [eassumption|].
        solve_DisjList.
      - apply invalidInv_other_midx_deqMsgs; auto.
        eapply DisjList_SubList; [eassumption|].
        solve_DisjList.
    Qed.

    Definition MsiSvMsgOutPred: MsgOutPred ImplOStateIfc :=
      fun eout oss orqs =>
        match case (sigOf eout) on sig_dec default True with
        | (ec1, (MRq, Spec.getRq)): False
        | (ec1, (MRq, Spec.setRq)): False
        | (ec1, (MRq, Spec.evictRq)): False
        | (ec2, (MRq, Spec.getRq)): False
        | (ec2, (MRq, Spec.setRq)): False
        | (ec2, (MRq, Spec.evictRq)): False

        | (c1pRq, (MRq, msiRqI)):
            corq1 <-- orqs@[child1Idx]; corq1@[upRq] <> None
        | (c2pRq, (MRq, msiRqI)):
            corq2 <-- orqs@[child2Idx]; corq2@[upRq] <> None
        | (c1pRq, (MRq, msiRqS)):
            cost1 <-- oss@[child1Idx];
            corq1 <-- orqs@[child1Idx];
            cost1#[implStatusIdx] = msiI /\ corq1@[upRq] <> None
        | (c2pRq, (MRq, msiRqS)):
            cost2 <-- oss@[child2Idx];
            corq2 <-- orqs@[child2Idx];
            cost2#[implStatusIdx] = msiI /\ corq2@[upRq] <> None
        | (c1pRq, (MRq, msiRqM)):
            cost1 <-- oss@[child1Idx];
            corq1 <-- orqs@[child1Idx];
            cost1#[implStatusIdx] <= msiS /\ corq1@[upRq] <> None
        | (c2pRq, (MRq, msiRqM)):
            cost2 <-- oss@[child2Idx];
            corq2 <-- orqs@[child2Idx];
            cost2#[implStatusIdx] <= msiS /\ corq2@[upRq] <> None

        | (pc1, (MRq, msiDownRqS)):
            post <-- oss@[parentIdx];
            porq <-- orqs@[parentIdx];
            msiM <= post#[implDirIdx].(fst) /\ porq@[downRq] <> None
        | (pc2, (MRq, msiDownRqS)):
            post <-- oss@[parentIdx];
            porq <-- orqs@[parentIdx];
            msiM <= post#[implDirIdx].(snd) /\ porq@[downRq] <> None
        | (pc1, (MRq, msiDownRqI)):
            post <-- oss@[parentIdx];
            porq <-- orqs@[parentIdx];
            msiS <= post#[implDirIdx].(fst) /\ porq@[downRq] <> None
        | (pc2, (MRq, msiDownRqI)):
            post <-- oss@[parentIdx];
            porq <-- orqs@[parentIdx];
            msiS <= post#[implDirIdx].(snd) /\ porq@[downRq] <> None

        | (pc1, (MRs, msiRsM)):
            post <-- oss@[parentIdx];
            post#[implStatusIdx] = msiI /\ post#[implDirIdx].(fst) = msiM
        | (pc2, (MRs, msiRsM)):
            post <-- oss@[parentIdx];
            post#[implStatusIdx] = msiI /\ post#[implDirIdx].(snd) = msiM

        | (pc1, (MRs, msiRsS)):
            post <-- oss@[parentIdx];
            post#[implStatusIdx] = msiS /\ post#[implDirIdx].(fst) = msiS
        | (pc2, (MRs, msiRsS)):
            post <-- oss@[parentIdx];
            post#[implStatusIdx] = msiS /\ post#[implDirIdx].(snd) = msiS
                              
        | (pc1, (MRs, msiRsI)):
            post <-- oss@[parentIdx];
            post#[implDirIdx].(fst) = msiI
        | (pc2, (MRs, msiRsI)):
            post <-- oss@[parentIdx];
            post#[implDirIdx].(snd) = msiI

        | (c1pRs, (MRs, msiDownRsI)):
            cost1 <-- oss@[child1Idx];
            cost1#[implStatusIdx] = msiI
        | (c2pRs, (MRs, msiDownRsI)):
            cost2 <-- oss@[child2Idx];
            cost2#[implStatusIdx] = msiI
        | (c1pRs, (MRs, msiDownRsS)):
            cost1 <-- oss@[child1Idx];
            cost1#[implStatusIdx] = msiS
        | (c2pRs, (MRs, msiDownRsS)):
            cost2 <-- oss@[child2Idx];
            cost2#[implStatusIdx] = msiS
        end.

    Ltac disc_GoodMsgOutPred :=
      repeat
        match goal with
        | [H: sigOf ?eout = (_, (_, _)) |- _] =>
          let midx := fresh "midx" in
          let msg := fresh "msg" in
          destruct eout as [midx msg]; inv H

        | [H: RsUpMsgFrom _ _ (_, _) |- _] =>
          let H1 := fresh "H" in
          let H2 := fresh "H" in
          destruct H as [H1 H2]; simpl in H1, H2
        | [H: RsDownMsgTo _ _ (_, _) |- _] =>
          let H1 := fresh "H" in
          let H2 := fresh "H" in
          destruct H as [H1 H2]; simpl in H1, H2
        | [H: RqUpMsgFrom _ _ (_, _) |- _] =>
          let H1 := fresh "H" in
          let H2 := fresh "H" in
          destruct H as [H1 H2]; simpl in H1, H2
        | [H: RqDownMsgTo _ _ (_, _) |- _] =>
          let H1 := fresh "H" in
          let H2 := fresh "H" in
          destruct H as [H1 H2]; simpl in H1, H2

        | [H: ~ In ?midx (sys_merqs _) |- _] =>
          elim H; simpl; tauto
        | [H1: msg_type ?msg = MRq, H2: msg_type ?msg = MRs |- _] =>
          rewrite H1 in H2; discriminate
        | [H: rsEdgeUpFrom _ ?oidx = Some ?rsUp |- _] =>
          is_var oidx;
          is_const rsUp;
          pose proof (rsEdgeUpFrom_indsOf _ _ H);
          dest_in; try discriminate
        | [H: edgeDownTo _ ?oidx = Some ?down |- _] =>
          is_var oidx;
          is_const down;
          pose proof (edgeDownTo_indsOf _ _ H);
          dest_in; try discriminate
        | [H: parentIdxOf _ ?oidx = Some ?pidx |- _] => progress simpl in H
        | [H: parentIdxOf _ ?oidx = Some ?pidx |- _] =>
          is_const oidx; is_var pidx; inv H
        end.

    Lemma msiSvMsgOutPred_good:
      GoodMsgOutPred topo MsiSvMsgOutPred.
    Proof.
      red; intros; repeat split.

      - do 2 (red; intros).
        red in H1; unfold caseDec in H1.
        repeat find_if_inside;
          try (exfalso; auto; fail);
          disc_GoodMsgOutPred.
        + red; unfold sigOf, valOf, snd; rewrite H5, H6; simpl.
          specialize (H2 _ (or_introl eq_refl)); dest.
          rewrite <-H, <-H0; assumption.
        + red; unfold sigOf, valOf, snd; rewrite H5, H6; simpl.
          specialize (H2 _ (or_introl eq_refl)); dest.
          rewrite <-H, <-H0; assumption.
        + red; unfold sigOf, valOf, snd; rewrite H5, H6; simpl.
          specialize (H2 _ (or_introl eq_refl)); dest.
          rewrite <-H, <-H0; assumption.
        + red; unfold sigOf, valOf, snd; rewrite H5, H6; simpl.
          specialize (H2 _ (or_introl eq_refl)); dest.
          rewrite <-H, <-H0; assumption.
        + red; unfold caseDec.
          repeat find_if_inside; congruence.

      - do 2 (red; intros).
        red in H0; unfold caseDec in H0.
        repeat find_if_inside;
          try (exfalso; auto; fail);
          disc_GoodMsgOutPred.
        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (In child1Idx (subtreeIndsOf topo child1Idx)) by (simpl; tauto).
          specialize (H1 _ H); dest.
          rewrite <-H1.
          assumption.
        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (In child2Idx (subtreeIndsOf topo child2Idx)) by (simpl; tauto).
          specialize (H1 _ H); dest.
          rewrite <-H1.
          assumption.
        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (In child1Idx (subtreeIndsOf topo child1Idx)) by (simpl; tauto).
          specialize (H1 _ H); dest.
          rewrite <-H1.
          assumption.
        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (In child2Idx (subtreeIndsOf topo child2Idx)) by (simpl; tauto).
          specialize (H1 _ H); dest.
          rewrite <-H1.
          assumption.
        + red; unfold caseDec.
          repeat find_if_inside; congruence.
    Qed.

    Lemma implInv_value_changed:
      forall oss orqs msgs,
        ImplInv {| bst_oss := oss;
                   bst_orqs := orqs;
                   bst_msgs := msgs |} ->
        forall cidx ost nv (noss: OStates ImplOStateIfc),
          oss@[cidx] = Some ost ->
          noss = oss +[cidx <- (nv, snd ost)] ->
          ImplInv {| bst_oss := noss;
                     bst_orqs := orqs;
                     bst_msgs := msgs |}.
    Proof.
      unfold ImplInv; simpl; intros.
      disc_rule_conds_ex.
    Qed.

    Ltac disc_rule_custom ::=
      try disc_footprints_ok;
      try disc_AtomicInv.

    Lemma msiSv_impl_InvTrs_init:
      forall st1,
        Reachable (steps step_m) impl st1 ->
        ImplInv st1 ->
        forall oidx ridx ins outs st2,
          SubList (idsOf ins) (sys_merqs impl) ->
          step_m impl st1 (RlblInt oidx ridx ins outs) st2 ->
          AtomicInv
            MsiSvMsgOutPred
            ins st1 [RlblInt oidx ridx ins outs] outs st2 /\
          ImplInv st2.
    Proof.
      intros.
      inv_step.
      pose proof (footprints_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys H) as Hftinv.
      pose proof (upLockInv_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree H) as Hulinv.
      pose proof (downLockInv_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree
                    msiSv_impl_GoodExtRssSys H) as Hdlinv.
      good_locking_get obj.
      dest_in.

      3, 7, 10, 13, 17, 20: atomic_init_exfalso_rs_from_parent.
      all: try (atomic_init_exfalso_rq; fail).

      - (** [childGetRqImm] *)
        disc_rule_conds_ex.
        simpl; split; [simpl; repeat constructor|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        replace (orqs +[child1Idx <- norq]) with orqs by meq.
        apply implInv_other_midx_enqMP; [|solve_not_in].
        apply implInv_other_midx_deqMP; [|solve_not_in].
        assumption.

      - (** [childGetRqS] *)
        disc_rule_conds_ex.
        simpl; split.
        + simpl; repeat constructor.
          solve_rule_conds_ex.
        + replace (oss +[child1Idx <- pos]) with oss by meq.
          apply implInv_other_msg_id_enqMP; [|solve_not_in].
          apply implInv_other_midx_deqMP; [|solve_not_in].
          eapply implInv_orqs_weakened in H0; try eassumption.
          findeq.

      - (** [childSetRqImm] *)
        disc_rule_conds_ex.
        simpl; split; [simpl; repeat constructor|].
        replace (orqs +[child1Idx <- norq]) with orqs by meq.
        apply implInv_other_midx_enqMP; [|solve_not_in].
        apply implInv_other_midx_deqMP; [|solve_not_in].
        eapply implInv_value_changed; eauto.

      - (** [childSetRqM] *)
        disc_rule_conds_ex.
        simpl; split.
        + simpl; repeat constructor.
          solve_rule_conds_ex.
        + replace (oss +[child1Idx <- pos]) with oss by meq.
          apply implInv_other_msg_id_enqMP; [|solve_not_in].
          apply implInv_other_midx_deqMP; [|solve_not_in].
          eapply implInv_orqs_weakened in H0; try eassumption.
          findeq.

      - (** [childEvictRqI] *)
        disc_rule_conds_ex.
        simpl; split.
        + simpl; repeat constructor.
          solve_rule_conds_ex.
        + replace (oss +[child1Idx <- pos]) with oss by meq.
          red in H0; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try discriminate.
          * solve_msi.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply msgExistsSig_enqMP_or in H24; destruct H24; [discriminate|].
            apply msgExistsSig_deqMP_inv in H24; auto.
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_enqMP.
            { apply invalidMsgs_deqMP; assumption. }
            { red; simpl; solve_msi. }
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.

    Admitted.

    Ltac disc_rule_custom ::=
      try disc_footprints_ok;
      try disc_msg_case;
      try disc_AtomicInv;
      try disc_minds_const.

    Local Hint Resolve msiSv_impl_ORqsInit.
    Local Hint Resolve msiSv_impl_RqRsSys.
    Local Hint Resolve msiSvMsgOutPred_good.

    Lemma invalidMsgs_if_rsDown_exists:
      forall st,
        Reachable (steps step_m) impl st ->
        forall cobj,
          In cobj impl.(sys_objs) ->
          forall orqs msgs oidx orq,
            cobj.(obj_idx) = oidx ->
            bst_msgs st = msgs ->
            UpLockInvORq topo orqs msgs oidx orq ->
            forall pc cpRq cpRs,
              parentIdxOf topo oidx = Some parentIdx ->
              edgeDownTo topo oidx = Some pc ->
              rqEdgeUpFrom topo oidx = Some cpRq ->
              rsEdgeUpFrom topo oidx = Some cpRs ->
              forall rsm,
                InMP pc rsm msgs ->
                msg_type rsm = MRs ->
                msg_id rsm <> msiRsS ->
                forall cost,
                  InvalidMsgs cost pc cpRq cpRs msgs.
    Proof.
      intros.
      red; intros.
      destruct idm as [midx msg].
      unfold caseDec.
      repeat find_if_inside.
      - inv e.
        exfalso_uplock_rs_two parentIdx pc msg rsm.
        intro Hx; subst; simpl in *; auto.
      - inv e.
        eapply rsDown_in_rsUp_in_false
          with (st0:= st) (rsdm:= rsm) (rsum:= msg)
               (pobj:= parent); eauto.
        simpl; tauto.
      - exfalso; inv e.
        exfalso_uplock_rq_rs parentIdx cpRq pc.
      - auto.
    Qed.

    Lemma invalidMsgs_rsUp_deq:
      forall st,
        Reachable (steps step_m) impl st ->
        forall cobj pobj,
          In cobj impl.(sys_objs) ->
          In pobj impl.(sys_objs) ->
          forall orqs msgs pidx orq,
            pobj.(obj_idx) = pidx ->
            bst_msgs st = msgs ->
            DownLockInvORq topo orqs msgs pidx orq ->
            forall cidx pc cpRq cpRs,
              cobj.(obj_idx) = cidx ->
              parentIdxOf topo cidx = Some pidx ->
              edgeDownTo topo cidx = Some pc ->
              rqEdgeUpFrom topo cidx = Some cpRq ->
              rsEdgeUpFrom topo cidx = Some cpRs ->
              forall rsm,
                FirstMP msgs cpRs rsm ->
                msg_type rsm = MRs ->
                forall cost: OState ImplOStateIfc,
                  cost#[implStatusIdx] = msiI ->
                  InvalidMsgs cost pc cpRq cpRs (deqMP cpRs msgs).
    Proof.
      intros.
      red; intros.
      destruct idm as [midx msg].
      unfold caseDec.
      repeat find_if_inside; auto.
      - inv e.
        eapply rsDown_in_rsUp_in_false
          with (st0:= st) (rsdm:= msg) (rsum:= rsm)
               (cobj0:= cobj) (pobj0:= pobj); eauto.
        + apply InMP_deqMP in H13; assumption.
        + apply FirstMP_InMP; assumption.
      - inv e.
        eapply rsUp_in_deqMP_false; eauto.
    Qed.

    Lemma msiSv_impl_InvTrs: InvTrs impl ImplInv.
    Proof.
      eapply inv_atomic_InvTrs;
        [red; intros; eapply msiSv_impl_InvTrs_ext_in; eauto
        |red; intros; eapply msiSv_impl_InvTrs_ext_out; eauto
        |].
      instantiate (1:= AtomicInv MsiSvMsgOutPred).
      red; intros.
      destruct H1.
      generalize dependent ist2.
      induction H3; simpl; intros; subst;
        [inv_steps; apply msiSv_impl_InvTrs_init; auto|].

      inv_steps.
      pose proof (reachable_steps H H9) as Hr1.
      pose proof (reachable_steps Hr1 (steps_singleton H11)) as Hr2.
      pose proof (footprints_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys Hr1) as Hftinv.
      pose proof (upLockInv_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree Hr1) as Hpulinv.
      pose proof (upLockInv_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree Hr2) as Hnulinv.
      pose proof (downLockInv_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree
                    msiSv_impl_GoodExtRssSys Hr1) as Hpdlinv.
      pose proof (downLockInv_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree
                    msiSv_impl_GoodExtRssSys Hr2) as Hndlinv.
      pose proof (implInvB_ok Hr1) as Hibinv.

      specialize (IHAtomic H1 _ H9); dest.
      inv_step; dest_in.

      11-20, 31-40: admit.
            
      (*! For 1-10: *)

      - (** [childGetRqImm] *) atomic_cont_exfalso_bound MsiSvMsgOutPred.
      - (** [childGetRqS] *) atomic_cont_exfalso_bound MsiSvMsgOutPred.

      - (** [childGetRsS] *)
        disc_rule_conds_ex.
        get_lock_minds child1Idx.

        disc_msg_preds H4.
        disc_rule_conds_ex.

        split.
        + pose proof H3.
          eapply atomic_rsDown_singleton with (oidx:= child1Idx) in H24;
            try exact H; eauto; [|red; auto].
          subst; rewrite removeOnce_nil; simpl.
          repeat constructor.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try solve_msi.
          * apply invalidMsgs_other_msg_id_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply msgExistsSig_enqMP_or in H36; destruct H36; [discriminate|].
            apply msgExistsSig_deqMP_inv in H36; auto.
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.

      - (** [childDownRqS] *)
        disc_rule_conds_ex.

        disc_msg_preds H4.
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * eapply atomic_rqDown_preserves_msg_out_preds;
              try exact H; eauto.
            red; auto.
          * repeat constructor.
            red; simpl.
            solve_rule_conds_ex.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try solve_msi.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP.
            assumption.

      - (** [childSetRqImm] *) atomic_cont_exfalso_bound MsiSvMsgOutPred.
      - (** [childSetRqM] *) atomic_cont_exfalso_bound MsiSvMsgOutPred.

      - (** [childSetRsM] *)
        disc_rule_conds_ex.
        get_lock_minds child1Idx.
        disc_rule_conds_ex.

        disc_msg_preds H4.
        disc_rule_conds_ex.

        clear Hnulinv Hpdlinv Hndlinv.
        get_lock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
        disc_rule_conds_ex.

        split.
        + pose proof H3.
          eapply atomic_rsDown_singleton with (oidx:= child1Idx) in H24;
            try exact H; eauto; [|red; auto].
          subst; rewrite removeOnce_nil; simpl.
          repeat constructor.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try solve_msi.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP.
            eapply invalidMsgs_if_rsDown_exists
              with (cobj:= child child1Idx ec1 ce1 c1pRq c1pRs pc1);
              try exact Hr1; try reflexivity; try eassumption.
            { simpl; tauto. }
            { apply FirstMP_InMP; assumption. }
            { rewrite H15; discriminate. }
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply msgExistsSig_enqMP_or in H37; destruct H37; [discriminate|].
            apply msgExistsSig_deqMP_inv in H37; auto.
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.

      - (** [childDownRqI] *)
        disc_rule_conds_ex.

        disc_msg_preds H4.
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * eapply atomic_rqDown_preserves_msg_out_preds;
              try exact H; eauto.
            red; auto.
          * repeat constructor.
            red; simpl; mred.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try solve_msi.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP.
            assumption.

      - (** [childEvictRqI] *) atomic_cont_exfalso_bound MsiSvMsgOutPred.
      - (** [childEvictRsI] *)
        disc_rule_conds_ex.
        get_lock_minds child1Idx.
        disc_rule_conds_ex.

        disc_msg_preds H4.
        disc_rule_conds_ex.

        clear Hnulinv Hpdlinv Hndlinv.
        get_lock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
        disc_rule_conds_ex.
        
        split.
        + pose proof H3.
          eapply atomic_rsDown_singleton with (oidx:= child1Idx) in H20;
            try exact H; eauto; [|red; auto].
          subst; rewrite removeOnce_nil; simpl.
          repeat constructor.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try solve_msi.
          * apply invalidMsgs_other_msg_id_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply msgExistsSig_enqMP_or in H36; destruct H36; [discriminate|].
            apply msgExistsSig_deqMP_inv in H36; auto.
          * left; reflexivity.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP.
            eapply invalidMsgs_if_rsDown_exists
              with (cobj:= child child1Idx ec1 ce1 c1pRq c1pRs pc1);
              try exact Hr1; try reflexivity; try eassumption.
            { simpl; tauto. }
            { apply FirstMP_InMP; assumption. }
            { rewrite H14; discriminate. }
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.

      (*! For 21-30: *)
      
      - (** [parentGetRqImm] *)
        disc_rule_conds_ex.

        disc_msg_preds H4.
        disc_rule_conds_ex.

        split.
        + pose proof H3.
          eapply atomic_rqUp_singleton with (oidx:= child1Idx) in H8;
            try exact H; eauto; [|red; auto].
          subst; rewrite removeOnce_nil; simpl.
          repeat constructor.
          red; simpl.
          solve_rule_conds_ex.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try solve_msi.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply msgExistsSig_enqMP_or in H31; destruct H31; [discriminate|].
            apply msgExistsSig_deqMP_inv in H31; auto.
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.

      - (** [parentGetDownRqS] *)
        disc_rule_conds_ex.

        unfold getDir in *; simpl in *.
        disc_msg_preds H4.
        disc_rule_conds_ex.

        split.
        + red in Hibinv.
          disc_rule_conds_ex.
          pose proof H3.
          eapply atomic_rqUp_singleton with (oidx:= child1Idx) in H30;
            try exact H; eauto; [|red; auto].
          subst; rewrite removeOnce_nil; simpl.
          repeat constructor.
          red; simpl.
          solve_rule_conds_ex.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false.
          * apply invalidMsgs_other_msg_id_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * left; assumption.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_msg_id_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
        
      - (** [parentSetRqImm] *)
        disc_rule_conds_ex.

        disc_msg_preds H4.
        disc_rule_conds_ex.

        clear Hnulinv Hpdlinv Hndlinv.
        get_lock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
        disc_rule_conds_ex.

        split.
        + pose proof H3.
          eapply atomic_rqUp_singleton with (oidx:= child1Idx) in H8;
            try exact H; eauto; [|red; auto].
          subst; rewrite removeOnce_nil; simpl.
          repeat constructor.
          red; simpl.
          solve_rule_conds_ex.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try solve_msi.
          * apply msgExistsSig_enqMP_or in H33; destruct H33; [discriminate|].
            apply msgExistsSig_deqMP_inv in H33.
            destruct H33 as [[midx msg] [? ?]]; simpl in *.
            inv H34.
            exfalso.
            exfalso_uplock_rq_two parentIdx c1pRq msg rmsg.
            { intro Hx; subst.
              rewrite H10 in H38; discriminate.
            }
            { apply FirstMP_InMP; assumption. }

          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply msgExistsSig_enqMP_or in H33; destruct H33; [discriminate|].
            apply msgExistsSig_deqMP_inv in H33; auto.
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.

      - (** [parentSetDownRqI] *)
        disc_rule_conds_ex.

        disc_msg_preds H4.
        disc_rule_conds_ex.

        split.
        + pose proof H3.
          eapply atomic_rqUp_singleton with (oidx:= child1Idx) in H8;
            try exact H; eauto; [|red; auto].
          subst; rewrite removeOnce_nil; simpl.
          repeat constructor.
          red; simpl.
          solve_rule_conds_ex.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try solve_msi.
          * apply invalidMsgs_other_msg_id_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_msg_id_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.

      - (** [parentGetDownRsS] *)
        disc_rule_conds_ex.

        disc_msg_preds H4.
        disc_rule_conds_ex.

        red in Hibinv.
        disc_rule_conds_ex.
        specialize (H21 eq_refl); dest.

        (** TODO: automate it! *)
        assert (exists corq1,
                   orqs@[child1Idx] = Some corq1 /\
                   corq1@[upRq] <> None).
        { clear Hnulinv Hpdlinv Hndlinv.
          get_lock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
          eapply upLockInvORq_parent_locked_locked in H34;
            try reflexivity; dest.
          { destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1;
              simpl in H33; [|mred].
            eauto.
          }
          { red; simpl.
            rewrite H17; simpl; eauto.
          }
        }
        destruct H33 as [corq1 [? ?]].

        split.
        + good_footprint_get parentIdx.
          disc_rule_conds.
          apply Forall_app.
          * simpl.
            red in H5; simpl in H5.
            rewrite <-H7 in H41.
            eapply atomic_rsUps_preserves_msg_out_preds
              with (rsUps:= [(c2pRs, rmsg)]) in H5;
              try exact H9; try eassumption; eauto.
            { right; right; left; reflexivity. }
            { reflexivity. }
            { repeat constructor; intro Hx; elim Hx. }
            { apply SubList_cons; [assumption|].
              apply SubList_nil.
            }
          * repeat constructor.
            red; simpl.
            solve_rule_conds_ex.
            
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try discriminate.
          * clear -H12; solve_msi.
          * clear -H12; solve_msi.
            
      - (** [parentGetDownRsI] *)
        disc_rule_conds_ex.

        disc_msg_preds H4.
        disc_rule_conds_ex.

        red in Hibinv.
        disc_rule_conds_ex.
        specialize (H21 eq_refl); dest.
        rewrite H21 in *.

        assert (exists corq1,
                   orqs@[child1Idx] = Some corq1 /\
                   corq1@[upRq] <> None).
        { clear Hnulinv Hpdlinv Hndlinv.
          get_lock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
          eapply upLockInvORq_parent_locked_locked in H34;
            try reflexivity; dest.
          { destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1;
              simpl in H33; [|mred].
            eauto.
          }
          { red; simpl.
            rewrite H17; simpl; eauto.
          }
        }
        destruct H33 as [corq1 [? ?]].

        split.
        + good_footprint_get parentIdx.
          disc_rule_conds.
          apply Forall_app.
          * simpl.
            red in H5; simpl in H5.
            rewrite <-H7 in H41.
            eapply atomic_rsUps_preserves_msg_out_preds
              with (rsUps:= [(c2pRs, rmsg)]) in H5;
              try exact H9; try eassumption; eauto.
            { right; right; left; reflexivity. }
            { reflexivity. }
            { repeat constructor; intro Hx; elim Hx. }
            { apply SubList_cons; [assumption|].
              apply SubList_nil.
            }
          * repeat constructor.
            red; simpl.
            solve_rule_conds_ex.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try discriminate.
          * clear -H12; solve_msi.
          * clear -H12; solve_msi.
          * exfalso.

            clear Hpulinv Hpdlinv Hndlinv.
            get_lock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
            destruct H46 as [[midx msg] ?]; dest; inv H47.

            (** TODO: [exfalso_uplock_rq_rs] doesn't work here.. *)
            (* exfalso_uplock_rq_rs parentIdx c1pRq pc1. *)
            eapply upLockInvORq_rqUp_down_rssQ_False with
                (pidx := parentIdx) (rqUp := c1pRq) (down := pc1) in H48;
              try reflexivity; auto.
            { eapply findQ_length_ge_one; try eassumption. }
            { eapply rssQ_length_ge_one; [|apply InMP_or_enqMP; eauto].
              reflexivity.
            }
          * left; assumption.
          * clear Hnulinv Hndlinv.
            get_lock_inv (child child2Idx ec2 ce2 c2pRq c2pRs pc2) impl.
            clear H47.

            (** TODO: make an Ltac for this. *)
            let H := fresh "H" in
            assert (H : In parent (sys_objs impl)) by (simpl; tauto);
              progress good_locking_get parent; clear H.
            clear H47.

            apply invalidMsgs_other_msg_id_enqMP; [|solve_not_in].
            eapply invalidMsgs_rsUp_deq
              with (cobj:= child child2Idx ec2 ce2 c2pRq c2pRs pc2)
                   (pobj:= parent);
              try exact Hr1; try eassumption; try reflexivity;
                try (simpl; tauto).

      - (** [parentEvictRqImmI] *)
        disc_rule_conds_ex.

        unfold getDir in *; simpl in *.
        disc_rule_conds_ex.

        split.
        + pose proof H3.
          eapply atomic_rqUp_singleton with (oidx:= child1Idx) in H7;
            try exact H; eauto; [|red; auto].
          subst; rewrite removeOnce_nil; simpl.
          repeat constructor.
          red; simpl.
          solve_rule_conds_ex.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try solve_msi.
          * apply invalidMsgs_other_msg_id_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply msgExistsSig_enqMP_or in H31; destruct H31; [discriminate|].
            apply msgExistsSig_deqMP_inv in H31; auto.
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_msg_id_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.

      - (** [parentEvictRqImmS] *)
        disc_rule_conds_ex.

        clear Hpulinv Hpdlinv Hndlinv.
        get_lock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
        disc_rule_conds_ex.

        disc_msg_preds H4.
        unfold getDir in *; simpl in *.
        disc_rule_conds_ex.

        split.
        + pose proof H3.
          eapply atomic_rqUp_singleton with (oidx:= child1Idx) in H7;
            try exact H; eauto; [|red; auto].
          subst; rewrite removeOnce_nil; simpl.
          repeat constructor.
          red; simpl.
          solve_rule_conds_ex.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try solve_msi.
          * right; eexists (_, _); split.
            { apply InMP_or_enqMP; left; simpl; eauto. }
            { reflexivity. }
          * eapply invalidMsgs_if_rsDown_exists
              with (cobj:= child child1Idx ec1 ce1 c1pRq c1pRs pc1);
              try exact Hr2; try eassumption; try reflexivity.
            { simpl; tauto. }
            { apply InMP_or_enqMP; left; auto. }
            { reflexivity. }
            { discriminate. }

      - (** [parentEvictRqImmLastS] *)
        disc_rule_conds_ex.

        clear Hpulinv Hpdlinv Hndlinv.
        get_lock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
        disc_rule_conds_ex.

        disc_msg_preds H4.
        unfold getDir in *; simpl in *.
        disc_rule_conds_ex.

        split.
        + pose proof H3.
          eapply atomic_rqUp_singleton with (oidx:= child1Idx) in H7;
            try exact H; eauto; [|red; auto].
          subst; rewrite removeOnce_nil; simpl.
          repeat constructor.
          red; simpl.
          solve_rule_conds_ex.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try solve_msi.
          * right; eexists (_, _); split.
            { apply InMP_or_enqMP; left; simpl; eauto. }
            { reflexivity. }
          * eapply invalidMsgs_if_rsDown_exists
              with (cobj:= child child1Idx ec1 ce1 c1pRq c1pRs pc1);
              try exact Hr2; try eassumption; try reflexivity.
            { simpl; tauto. }
            { apply InMP_or_enqMP; left; auto. }
            { reflexivity. }
            { discriminate. }
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.

      - (** [parentEvictRqImmM] *)
        disc_rule_conds_ex.

        clear Hpulinv Hpdlinv Hndlinv.
        get_lock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
        disc_rule_conds_ex.

        disc_msg_preds H4.
        unfold getDir in *; simpl in *.
        disc_rule_conds_ex.

        red in Hibinv.
        disc_rule_conds_ex.

        split.
        + pose proof H3.
          eapply atomic_rqUp_singleton with (oidx:= child1Idx) in H30;
            try exact H; eauto; [|red; auto].
          subst; rewrite removeOnce_nil; simpl.
          repeat constructor.
          red; simpl.
          solve_rule_conds_ex.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * exfalso; solve_msi.
          * right; eexists (_, _); split.
            { apply InMP_or_enqMP; left; simpl; eauto. }
            { reflexivity. }
          * eapply invalidMsgs_if_rsDown_exists
              with (cobj:= child child1Idx ec1 ce1 c1pRq c1pRs pc1);
              try exact Hr2; try eassumption; try reflexivity.
            { simpl; tauto. }
            { apply InMP_or_enqMP; left; auto. }
            { reflexivity. }
            { discriminate. }
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.

    Admitted.

    Lemma implInv_init:
      ImplInv (initsOf impl).
    Proof.
      red; simpl.
      unfold implOStatesInit, implORqsInit; mred.
      simpl; repeat split;
        try (red; simpl; mred; solve_msi; fail).
    Qed.

    Lemma implInv_invStep:
      InvStep impl step_m ImplInv.
    Proof.
      apply invSeq_serializable_invStep.
      - apply implInv_init.
      - apply inv_trs_seqSteps.
        apply msiSv_impl_InvTrs.
      - eapply rqrs_Serializable.
        + apply msiSv_impl_ORqsInit.
        + apply msiSv_impl_RqRsSys.
    Qed.

  End Facts.
  
End Inv.

Hint Unfold ImplOStateMSI ChildExcl DirExcl ExclInv InvalidInv
     DirSound1 DirSound2 DirSoundS DirExcl1 DirExcl2
     DirCorrectM DirCorrectS DirInv
     ParentDownRsS1 ParentDownRsS2 ParentDownRsI1 ParentDownRsI2
     ParentDownLockBack DownLockInv
     ImplInv: RuleConds.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

