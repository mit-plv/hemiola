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

(*! TODO: move to another file for general use *)

Ltac disc_AtomicInv :=
  repeat
    match goal with
    | [H: AtomicInv _ _ _ _ _ _ |- _] => red in H; dest
    end.

Ltac atomic_cont_exfalso_bound msgOutPred :=
  exfalso;
  disc_rule_conds_ex;
  repeat 
    match goal with
    | [H1: AtomicMsgOutsInv _ ?eouts _, H2: In _ ?eouts |- _] =>
      red in H1; rewrite Forall_forall in H1;
      specialize (H1 _ H2); simpl in H1
    | [H: msgOutPred _ _ _ |- _] => red in H
    | [H1: caseDec _ ?sig _ _ |- _] =>
      match sig with
      | sigOf (?midx, ?msg) =>
        match goal with
        | [H2: msg_id ?msg = ?mid, H3: msg_type ?msg = ?mty |- _] =>
          progress replace sig with (midx, (mty, mid)) in H1
            by (unfold sigOf; simpl; rewrite H2, H3; reflexivity);
          simpl in H1
        end
      end
    end;
  assumption.

Ltac atomic_init_exfalso_rq :=
  exfalso;
  disc_rule_conds_ex;
  repeat
    match goal with
    | [H: _ = _ \/ _ |- _] =>
      destruct H; [subst; try discriminate|auto]
    end.

Ltac atomic_init_exfalso_rs_from_parent :=
  exfalso;
  repeat
    (repeat match goal with
            | [H: UpLockInvORq _ _ _ _ _ |- _] => red in H
            | [H1: ?orq@[0] = Some _, H2: context[?orq@[0]] |- _] =>
              rewrite H1 in H2; simpl in H2
            | [H: UpLockRsFromParent _ _ _ |- _] =>
              let rsFrom := fresh "rsFrom" in
              destruct H as [rsFrom [? ?]]
            end;
     disc_rule_conds_ex);
  repeat
    match goal with
    | [H1: _ = ?rsFrom \/ _, H2: edgeDownTo _ _ = Some ?rsFrom |- _] =>
      destruct H1; [subst; try discriminate|auto]
    end.

Ltac atomic_init_solve_AtomicMsgOutsInv :=
  simpl; repeat constructor.

Ltac atomic_init_solve_AtomicInv :=
  atomic_init_solve_AtomicMsgOutsInv.

Ltac disc_sig_caseDec :=
  match goal with
  | [H1: caseDec _ ?sig _ _ |- _] =>
    match sig with
    | sigOf (?midx, ?msg) =>
      match goal with
      | [H2: msg_id ?msg = ?mid, H3: msg_type ?msg = ?mty |- _] =>
        progress replace sig with (midx, (mty, mid)) in H1
          by (unfold sigOf; simpl; rewrite H2, H3; reflexivity);
        simpl in H1
      end
    end
  end.

Ltac disc_msg_preds_with Hl Hin :=
  match type of Hl with
  | AtomicMsgOutsInv _ ?eouts _ =>
    red in Hl; rewrite Forall_forall in Hl;
    specialize (Hl _ Hin); simpl in Hl;
    red in Hl; disc_sig_caseDec
  end.

Ltac disc_msg_preds Hin :=
  match goal with
  | [H: AtomicMsgOutsInv _ _ _ |- _] =>
    let Hl := fresh "H" in
    pose proof H as Hl;
    disc_msg_preds_with Hl Hin
  end.

Ltac pull_uplock_minds oidx :=
  progress (good_footprint_get oidx);
  repeat
    match goal with
    | [H: FootprintUpOkEx _ _ _ |- _] =>
      let rqFrom := fresh "rqFrom" in
      let rqTo := fresh "rqTo" in
      let rsFrom := fresh "rsFrom" in
      let rsbTo := fresh "rsbTo" in
      destruct H as [rqFrom [rqTo [rsFrom [rsbTo ?]]]]; dest;
      disc_rule_conds_ex
    | [H: parentIdxOf _ _ = Some ?oidx |- _] =>
      is_const oidx;
      pose proof (parentIdxOf_child_indsOf _ _ H);
      dest_in; try discriminate; simpl in *; clear H
    | [H: rqEdgeUpFrom _ ?oidx = Some _ |- _] =>
      is_const oidx; inv H
    | [H: rsEdgeUpFrom _ ?oidx = Some _ |- _] =>
      is_const oidx; inv H
    | [H: edgeDownTo _ ?oidx = Some _ |- _] =>
      is_const oidx; inv H
    end.

Ltac pull_uplock_inv obj sys :=
  let H := fresh "H" in
  assert (In obj (sys_objs sys)) as H by (simpl; tauto);
  progress (good_locking_get obj);
  clear H.

Ltac exfalso_uplock_rq_rs pidx' rqUp' down' :=
  progress
    match goal with
    | [H: UpLockInvORq _ _ _ _ _ |- _] =>
      eapply upLockInvORq_rqUp_down_rssQ_False
        with (pidx:= pidx') (rqUp:= rqUp') (down:= down') in H;
      try reflexivity; auto
    end;
  repeat
    match goal with
    | [ |- Datatypes.length (findQ _ _) >= 1] =>
      eapply findQ_length_ge_one; try eassumption
    | [ |- Datatypes.length (rssQ _ _) >= 1] =>
      eapply rssQ_length_ge_one; try eassumption
    | [H: FirstMPI _ (?midx, _) |- InMP ?midx _ _] =>
      apply FirstMP_InMP; eassumption
    end.

Ltac exfalso_uplock_rs_two pidx' down' msg :=
  progress
    match goal with
    | [H: UpLockInvORq _ _ _ _ _ |- _] =>
      eapply upLockInvORq_down_rssQ_length_two_False
        with (pidx:= pidx') (down:= down') in H;
      try reflexivity; auto
    end;
  repeat
    match goal with
    | [ |- Datatypes.length (rssQ (enqMP _ ?omsg _) _) >= 2] =>
      eapply rssQ_length_two with (msg1:= omsg) (msg2:= msg);
      try eassumption; auto
    | [ |- _ <> _] => intro Hx; subst; simpl in *; discriminate
    | [ |- InMP ?midx ?msg (enqMP ?midx ?msg _)] =>
      apply InMP_or_enqMP; left; auto
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
              (cost: OState ImplOStateIfc)
              (corq: ORq Msg)
              (pc cpRq cpRs: IdxT)
              (msgs: MessagePool Msg).

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
              (corq1 corq2: ORq Msg).

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

    Definition DirInv: Prop :=
      DirSound1 /\ DirSound2.

  End InvDir.

  Definition ImplInv (st: MState ImplOStateIfc): Prop :=
    post <-- (bst_oss st)@[parentIdx];
      cost1 <-- (bst_oss st)@[child1Idx];
      cost2 <-- (bst_oss st)@[child2Idx];
      porq <-- (bst_orqs st)@[parentIdx];
      corq1 <-- (bst_orqs st)@[child1Idx];
      corq2 <-- (bst_orqs st)@[child2Idx];
      DirInv post cost1 cost2 corq1 corq2 /\
      ExclInv post#[implDirIdx].(fst) cost1 corq1 pc1 c1pRq c1pRs (bst_msgs st) /\
      ExclInv post#[implDirIdx].(snd) cost2 corq2 pc2 c2pRq c2pRs (bst_msgs st) /\
      InvalidInv post#[implDirIdx].(fst) cost1 pc1 c1pRq c1pRs (bst_msgs st) /\
      InvalidInv post#[implDirIdx].(snd) cost2 pc2 c2pRq c2pRs (bst_msgs st).

  Hint Unfold ImplOStateMSI ChildExcl DirExcl ExclInv InvalidInv
       DirSound1 DirSound2 DirInv: RuleConds.

  Section Facts.

    Lemma dirInv_orqs_weakened_1:
      forall post cost1 cost2 corq1 corq2,
        DirInv post cost1 cost2 corq1 corq2 ->
        forall rty rqi,
          DirInv post cost1 cost2 (corq1 +[rty <- rqi]) corq2.
    Proof.
      unfold DirInv; intros; dest.
      split; [|assumption].
      red in H; red; mred.
    Qed.

    Lemma dirInv_orqs_weakened_2:
      forall post cost1 cost2 corq1 corq2,
        DirInv post cost1 cost2 corq1 corq2 ->
        forall rty rqi,
          DirInv post cost1 cost2 corq1 (corq2 +[rty <- rqi]).
    Proof.
      unfold DirInv; intros; dest.
      split; [assumption|].
      red in H0; red; mred.
    Qed.

    Lemma exclInv_orqs_weakened:
      forall dir cost corq pc cpRq cpRs msgs,
        ExclInv dir cost corq pc cpRq cpRs msgs ->
        forall rty rqi,
          ExclInv dir cost (corq +[rty <- rqi]) pc cpRq cpRs msgs.
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
        + apply dirInv_orqs_weakened_1; assumption.
        + apply exclInv_orqs_weakened; assumption.
      - repeat ssplit; try assumption.
        + apply dirInv_orqs_weakened_2; assumption.
        + apply exclInv_orqs_weakened; assumption.
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

    Lemma exclInv_other_midx_enqMP:
      forall dir cost corq pc cpRq cpRs msgs,
        ExclInv dir cost corq pc cpRq cpRs msgs ->
        forall midx msg,
          ~ In midx [pc; cpRq; cpRs] ->
          ExclInv dir cost corq pc cpRq cpRs (enqMP midx msg msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split; intros.
      - apply invalidMsgs_other_midx_enqMP; auto.
      - apply H1; auto.
        apply msgExistsSig_enqMP_or in H3.
        destruct H3; auto.
        inv H3; exfalso; auto.
    Qed.

    Lemma exclInv_other_midx_enqMsgs:
      forall dir cost corq pc cpRq cpRs msgs,
        ExclInv dir cost corq pc cpRq cpRs msgs ->
        forall nmsgs,
          DisjList (idsOf nmsgs) [pc; cpRq; cpRs] ->
          ExclInv dir cost corq pc cpRq cpRs (enqMsgs nmsgs msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split; intros.
      - apply invalidMsgs_other_midx_enqMsgs; auto.
      - apply H1; auto.
        apply msgExistsSig_enqMsgs_or in H3.
        destruct H3; auto.
        destruct H3 as [[midx msg] [? ?]].
        inv H4.
        apply in_map with (f:= idOf) in H3.
        exfalso; eapply DisjList_In_1; eauto.
        simpl; tauto.
    Qed.

    Lemma exclInv_other_msg_id_enqMP:
      forall dir cost corq pc cpRq cpRs msgs,
        ExclInv dir cost corq pc cpRq cpRs msgs ->
        forall midx msg,
          ~ In msg.(msg_id) [msiRsS; msiDownRsS; msiRqI] ->
          ExclInv dir cost corq pc cpRq cpRs (enqMP midx msg msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split; intros.
      - apply invalidMsgs_other_msg_id_enqMP; auto.
      - apply H1; auto.
        apply msgExistsSig_enqMP_or in H3.
        destruct H3; auto.
        inv H3; exfalso; auto.
    Qed.

    Lemma exclInv_other_msg_id_enqMsgs:
      forall dir cost corq pc cpRq cpRs msgs,
        ExclInv dir cost corq pc cpRq cpRs msgs ->
        forall nmsgs,
          DisjList (map (fun idm => (valOf idm).(msg_id)) nmsgs)
                   [msiRsS; msiDownRsS; msiRqI] ->
          ExclInv dir cost corq pc cpRq cpRs (enqMsgs nmsgs msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split; intros.
      - apply invalidMsgs_other_msg_id_enqMsgs; auto.
      - apply H1; auto.
        apply msgExistsSig_enqMsgs_or in H3.
        destruct H3; auto.
        destruct H3 as [[midx msg] [? ?]].
        inv H4.
        apply in_map with (f:= fun idm => (valOf idm).(msg_id)) in H3.
        simpl in H3; rewrite H8 in H3.
        exfalso; eapply DisjList_In_1; eauto.
        simpl; tauto.
    Qed.

    Lemma exclInv_other_midx_deqMP:
      forall dir cost corq pc cpRq cpRs msgs,
        ExclInv dir cost corq pc cpRq cpRs msgs ->
        forall rmidx,
          ~ In rmidx [pc; cpRq; cpRs] ->
          ExclInv dir cost corq pc cpRq cpRs (deqMP rmidx msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split; intros.
      - apply invalidMsgs_deqMP; auto.
      - apply H1; auto.
        apply msgExistsSig_deqMP_inv in H3; auto.
    Qed.

    Lemma exclInv_other_midx_deqMsgs:
      forall dir cost corq pc cpRq cpRs msgs,
        ExclInv dir cost corq pc cpRq cpRs msgs ->
        forall rminds,
          DisjList rminds [pc; cpRq; cpRs] ->
          ExclInv dir cost corq pc cpRq cpRs (deqMsgs rminds msgs).
    Proof.
      intros.
      disc_rule_conds_ex.
      repeat split; intros.
      - apply invalidMsgs_deqMsgs; auto.
      - apply H1; auto.
        apply msgExistsSig_deqMsgs_inv in H3; auto.
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
        end.

    Lemma msiSvMsgOutPred_good:
      GoodMsgOutPred topo impl MsiSvMsgOutPred.
    Proof.
      red; intros; repeat split.

      - do 2 (red; intros).
        red in H0; unfold caseDec in H0.
        repeat find_if_inside;
          try (exfalso; auto; fail);
          disc_GoodMsgOutPred.
        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (In child1Idx (subtreeIndsOf topo child1Idx))
            by (simpl; tauto).
          specialize (H1 _ H).
          destruct H1; rewrite <-H1.
          assumption.
        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (In child2Idx (subtreeIndsOf topo child2Idx))
            by (simpl; tauto).
          specialize (H1 _ H).
          destruct H1; rewrite <-H1.
          assumption.
        + red; unfold caseDec.
          repeat find_if_inside; congruence.

      - do 2 (red; intros).
        red in H0; unfold caseDec in H0.
        repeat find_if_inside;
          try (exfalso; auto; fail);
          disc_GoodMsgOutPred.
        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (~ In parentIdx (subtreeIndsOf topo child1Idx)).
          { intro Hx; dest_in; discriminate. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1.
          assumption.
        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (~ In parentIdx (subtreeIndsOf topo child2Idx)).
          { intro Hx; dest_in; discriminate. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1.
          assumption.

        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (~ In parentIdx (subtreeIndsOf topo child1Idx)).
          { intro Hx; dest_in; discriminate. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1.
          assumption.
        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (~ In parentIdx (subtreeIndsOf topo child2Idx)).
          { intro Hx; dest_in; discriminate. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1.
          assumption.

        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (~ In parentIdx (subtreeIndsOf topo child1Idx)).
          { intro Hx; dest_in; discriminate. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1.
          assumption.
        + red; unfold sigOf, valOf, snd; rewrite H4, H5; simpl.
          assert (~ In parentIdx (subtreeIndsOf topo child2Idx)).
          { intro Hx; dest_in; discriminate. }
          specialize (H1 _ H).
          destruct H1; rewrite <-H1.
          assumption.
        + red; unfold caseDec.
          repeat find_if_inside; congruence.
          
      - red; intros.
        destruct (in_dec eq_nat_dec (idOf eout) (sys_merqs impl)); auto.
        right; intros.
        red; unfold caseDec.
        repeat find_if_inside; disc_GoodMsgOutPred.
        auto.

      - red; intros.
        red; unfold caseDec.
        repeat find_if_inside; disc_GoodMsgOutPred.
        auto.
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
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        replace (orqs +[child1Idx <- norq]) with orqs by meq.
        apply implInv_other_midx_enqMP; [|solve_not_in].
        apply implInv_other_midx_deqMP; [|solve_not_in].
        assumption.

      - (** [childGetRqS] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        apply implInv_other_msg_id_enqMP; [|solve_not_in].
        apply implInv_other_midx_deqMP; [|solve_not_in].
        eapply implInv_orqs_weakened in H0; try eassumption.
        findeq.

      - (** [childSetRqImm] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (orqs +[child1Idx <- norq]) with orqs by meq.
        admit.

      - (** [childSetRqM] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        apply implInv_other_msg_id_enqMP; [|solve_not_in].
        apply implInv_other_midx_deqMP; [|solve_not_in].
        eapply implInv_orqs_weakened in H0; try eassumption.
        findeq.

      - (** [childEvictRqI] *)
        disc_rule_conds_ex.
        simpl; split; [atomic_init_solve_AtomicInv|].
        replace (oss +[child1Idx <- pos]) with oss by meq.
        admit.

    Admitted.

    Ltac disc_rule_custom ::=
      try disc_footprints_ok;
      try disc_msg_case;
      try disc_AtomicInv;
      (* try disc_msi; *)
      try disc_minds_const.

    Local Hint Resolve msiSv_impl_ORqsInit.
    Local Hint Resolve msiSv_impl_RqRsSys.
    Local Hint Resolve msiSvMsgOutPred_good.

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
      pose proof (footprints_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    (reachable_steps H H9))
        as Hftinv.
      pose proof (upLockInv_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree (reachable_steps H H9)) as Hulinv.
      pose proof (downLockInv_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree
                    msiSv_impl_GoodExtRssSys (reachable_steps H H9)) as Hdlinv.

      specialize (IHAtomic H1 _ H9); dest.
      inv_step; dest_in.

      - (** [childGetRqImm] *) atomic_cont_exfalso_bound MsiSvMsgOutPred.
      - (** [childGetRqS] *) atomic_cont_exfalso_bound MsiSvMsgOutPred.

      - (** [childGetRsS] *)
        disc_rule_conds_ex.
        pull_uplock_minds child1Idx.

        disc_msg_preds H4.
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rsDown_preserves_msg_out_preds; eauto.
            red; auto.
          * repeat constructor.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try solve_msi.
          * apply invalidMsgs_other_msg_id_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply msgExistsSig_enqMP_or in H33; destruct H33; [discriminate|].
            apply msgExistsSig_deqMP_inv in H29; auto.
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.

      - (** [childDownRqS] *)
        disc_rule_conds_ex.

        split.
        + apply Forall_app.
          * apply forall_removeOnce.
            eapply atomic_rqDown_preserves_msg_out_preds; eauto.
            red; auto.
          * repeat constructor.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try solve_msi.
          * exfalso.
            destruct H26 as [[midx msg] [? ?]].
            inv H26.
            admit.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply msgExistsSig_enqMP_or in H26; destruct H26; [discriminate|].
            apply msgExistsSig_deqMP_inv in H20; auto.
          * (* TODO. predicate message for rqs. *)
            admit.
          * admit.
          * admit.
          * admit.

      - (** [childSetRqImm] *) atomic_cont_exfalso_bound MsiSvMsgOutPred.
      - (** [childSetRqM] *) atomic_cont_exfalso_bound MsiSvMsgOutPred.

      - (** [childSetRsM] *)
        disc_rule_conds_ex.
        pull_uplock_minds child1Idx.

        disc_msg_preds H4.
        disc_rule_conds_ex.

        split.
        + admit.
        + red in H6; red.
          disc_rule_conds_ex.
          intuition idtac; try solve_msi_false; try solve_msi.
          * admit.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.
          * apply msgExistsSig_enqMP_or in H33; destruct H33; [discriminate|].
            apply msgExistsSig_deqMP_inv in H29; auto.
          * apply childInvalid_enqMP.
            apply childInvalid_other_midx_deqMP; [|discriminate].
            assumption.
          * apply invalidMsgs_other_midx_enqMP; [|solve_not_in].
            apply invalidMsgs_deqMP; assumption.

      - (** [childDownRqI] *)
        admit.

      - (** [childEvictRqI] *) atomic_cont_exfalso_bound MsiSvMsgOutPred.
      - (** [childEvictRsI] *)
        admit.

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

