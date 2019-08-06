Require Import Bool List String Peano_dec Lia.
Require Import Common FMap HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Ex.Msi Ex.SpecSv.
Require Import Ex.MsiSv.MsiSv Ex.MsiSv.MsiSvTopo
        Ex.MsiSv.MsiSvInvB Ex.MsiSv.MsiSvInv.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Section Sim.

  Existing Instance MsiSv.ImplOStateIfc.

  Local Definition spec := SpecSv.spec 1.
  Local Definition impl := MsiSv.impl.

  (** Simulation between states *)

  Section DirCoh.
    Variables (cv: nat)
              (dir: MSI)
              (cost: OState)
              (corq: ORq Msg)
              (pc cpRq cpRs: IdxT)
              (msgs: MessagePool Msg).

    Definition DirMsgCoh (idm: Id Msg) :=
      match case (sigOf idm) on sig_dec default True with
      | (pc, (MRs, msiRsS)): (valOf idm).(msg_value) = cv
      | (cpRs, (MRs, msiDownRsS)): (valOf idm).(msg_value) = cv
      | (cpRq, (MRq, msiRqI)):
          (msiS <= cost#[implStatusIdx] -> (valOf idm).(msg_value) = cv)
      end.
    
    Definition DirMsgsCoh :=
      forall idm, InMPI msgs idm -> DirMsgCoh idm.

    Definition DirCoh :=
      msiS <= dir -> ImplOStateMSI cv cost /\ DirMsgsCoh.

  End DirCoh.

  Definition ImplStateCoh (cv: nat) (st: MState): Prop :=
    post <-- (bst_oss st)@[parentIdx];
      cost1 <-- (bst_oss st)@[child1Idx];
      cost2 <-- (bst_oss st)@[child2Idx];
      corq1 <-- (bst_orqs st)@[child1Idx];
      corq2 <-- (bst_orqs st)@[child2Idx];
      ImplOStateMSI cv post /\
      DirCoh cv post#[implDirIdx].(fst) cost1 pc1 c1pRq c1pRs (bst_msgs st) /\
      DirCoh cv post#[implDirIdx].(snd) cost2 pc2 c2pRq c2pRs (bst_msgs st).

  Definition SpecStateCoh (cv: nat) (st: @MState SpecOStateIfc): Prop :=
    sost <-- (bst_oss st)@[specIdx];
      sorq <-- (bst_orqs st)@[specIdx];
      sost#[specValueIdx] = cv.

  Inductive SimState: MState -> @MState SpecOStateIfc -> Prop :=
  | SimStateIntro:
      forall cv ist sst,
        SpecStateCoh cv sst ->
        ImplStateCoh cv ist ->
        SimState ist sst.

  Definition SimExtMP (imsgs: MessagePool Msg) (iorqs: ORqs Msg)
             (smsgs: MessagePool Msg) :=
    corq1 <-- iorqs@[child1Idx];
      corq2 <-- iorqs@[child2Idx];
      (corq1@[upRq] >>= (fun rqiu1 => rqiu1.(rqi_msg)))
        ::> (findQ ec1 imsgs) = findQ (erq 0) smsgs /\
      (corq2@[upRq] >>= (fun rqiu2 => rqiu2.(rqi_msg)))
        ::> (findQ ec2 imsgs) = findQ (erq 1) smsgs /\
      findQ ce1 imsgs = findQ (ers 0) smsgs /\
      findQ ce2 imsgs = findQ (ers 1) smsgs.
  
  Definition SimMSI (ist: MState) (sst: @MState SpecOStateIfc): Prop :=
    SimState ist sst /\
    SimExtMP ist.(bst_msgs) ist.(bst_orqs) sst.(bst_msgs).

  Hint Unfold DirCoh ImplStateCoh: RuleConds.

  Section Facts.

    Lemma simMsiSv_init:
      SimMSI (initsOf impl) (initsOf spec).
    Proof.
      split.
      - apply SimStateIntro with (cv:= 0).
        + reflexivity.
        + repeat split; vm_compute; intros; exfalso; auto.
      - repeat split.
    Qed.

    Lemma SimExtMP_enqMsgs:
      forall eins,
        NoDup (idsOf eins) ->
        forall imsgs orqs smsgs,
          SimExtMP imsgs orqs smsgs ->
          SimExtMP (enqMsgs eins imsgs) orqs (enqMsgs eins smsgs).
    Proof.
      unfold SimExtMP; intros.
      disc_rule_conds_ex.
      repeat split.
      - destruct (in_dec idx_dec ec1 (idsOf eins)).
        + apply in_map_iff in i.
          destruct i as [[midx msg] ?]; dest; simpl in *; subst.
          do 2 (erewrite findQ_In_NoDup_enqMsgs; eauto).
          rewrite ocons_app; congruence.
        + do 2 (rewrite findQ_not_In_enqMsgs by assumption).
          assumption.
      - destruct (in_dec idx_dec ec2 (idsOf eins)).
        + apply in_map_iff in i.
          destruct i as [[midx msg] ?]; dest; simpl in *; subst.
          do 2 (erewrite findQ_In_NoDup_enqMsgs; eauto).
          rewrite ocons_app; congruence.
        + do 2 (rewrite findQ_not_In_enqMsgs by assumption).
          assumption.
      - destruct (in_dec idx_dec ce1 (idsOf eins)).
        + apply in_map_iff in i.
          destruct i as [[midx msg] ?]; dest; simpl in *; subst.
          do 2 (erewrite findQ_In_NoDup_enqMsgs; eauto).
          congruence.
        + do 2 (rewrite findQ_not_In_enqMsgs by assumption).
          assumption.
      - destruct (in_dec idx_dec ce2 (idsOf eins)).
        + apply in_map_iff in i.
          destruct i as [[midx msg] ?]; dest; simpl in *; subst.
          do 2 (erewrite findQ_In_NoDup_enqMsgs; eauto).
          congruence.
        + do 2 (rewrite findQ_not_In_enqMsgs by assumption).
          assumption.
    Qed.

    Lemma SimExtMP_orqs:
      forall imsgs orqs1 orqs2 smsgs,
        SimExtMP imsgs orqs1 smsgs ->
        orqs1@[child1Idx] = orqs2@[child1Idx] ->
        orqs1@[child2Idx] = orqs2@[child2Idx] ->
        SimExtMP imsgs orqs2 smsgs.
    Proof.
      unfold SimExtMP; intros.
      disc_rule_conds_ex.
    Qed.

    Lemma SimExtMP_enqMP:
      forall midx msg imsgs orqs smsgs,
        SimExtMP imsgs orqs smsgs ->
        SimExtMP (enqMP midx msg imsgs) orqs (enqMP midx msg smsgs).
    Proof.
      intros.
      eapply SimExtMP_enqMsgs with (eins:= [(midx, msg)]) in H; auto.
      repeat constructor; intro; dest_in.
    Qed.

    Lemma SimExtMP_ext_outs_deqMsgs:
      forall eouts,
        ValidMsgsExtOut impl eouts ->
        forall imsgs orqs smsgs,
          Forall (FirstMPI imsgs) eouts ->
          SimExtMP imsgs orqs smsgs ->
          SimExtMP (deqMsgs (idsOf eouts) imsgs) orqs (deqMsgs (idsOf eouts) smsgs).
    Proof.
      unfold SimExtMP; intros.
      disc_rule_conds_ex.
      repeat split.
      - destruct (in_dec idx_dec ec1 (idsOf eouts)).
        + exfalso.
          destruct H; apply H in i.
          dest_in; discriminate.
        + do 2 (rewrite findQ_not_In_deqMsgs by assumption).
          assumption.
      - destruct (in_dec idx_dec ec2 (idsOf eouts)).
        + exfalso.
          destruct H; apply H in i.
          dest_in; discriminate.
        + do 2 (rewrite findQ_not_In_deqMsgs by assumption).
          assumption.
      - destruct (in_dec idx_dec ce1 (idsOf eouts)).
        + assert (findQ ce1 imsgs <> nil).
          { apply in_map_iff in i.
            destruct i as [[midx msg] ?]; dest; simpl in *; subst.
            intro Hx.
            rewrite Forall_forall in H0; specialize (H0 _ H6).
            eapply FirstMP_findQ_False; eauto.
          }
          assert (findQ (ers 0) smsgs <> nil) by congruence.
          eapply findQ_In_NoDup_deqMsgs in H5; eauto; [|apply H].
          destruct H5 as [ieout ?].
          eapply findQ_In_NoDup_deqMsgs in H6; eauto; [|apply H].
          destruct H6 as [seout ?].
          congruence.
        + do 2 (rewrite findQ_not_In_deqMsgs by assumption).
          assumption.
      - destruct (in_dec idx_dec ce2 (idsOf eouts)).
        + assert (findQ ce2 imsgs <> nil).
          { apply in_map_iff in i.
            destruct i as [[midx msg] ?]; dest; simpl in *; subst.
            intro Hx.
            rewrite Forall_forall in H0; specialize (H0 _ H6).
            eapply FirstMP_findQ_False; eauto.
          }
          assert (findQ (ers 1) smsgs <> nil) by congruence.
          eapply findQ_In_NoDup_deqMsgs in H5; eauto; [|apply H].
          destruct H5 as [ieout ?].
          eapply findQ_In_NoDup_deqMsgs in H6; eauto; [|apply H].
          destruct H6 as [seout ?].
          congruence.
        + do 2 (rewrite findQ_not_In_deqMsgs by assumption).
          assumption.
    Qed.

    Lemma SimExtMP_ext_outs_FirstMPI:
      forall eouts,
        ValidMsgsExtOut impl eouts ->
        forall imsgs orqs smsgs,
          SimExtMP imsgs orqs smsgs ->
          Forall (FirstMPI imsgs) eouts ->
          Forall (FirstMPI smsgs) eouts.
    Proof.
      unfold SimExtMP; intros.
      destruct H.
      disc_rule_conds_ex.
      apply Forall_forall; intros [midx msg] ?.
      rewrite Forall_forall in H1; specialize (H1 _ H6).
      apply in_map with (f:= idOf) in H6.
      apply H in H6; unfold idOf, fst in H6; dest_in.
      - unfold FirstMPI, FirstMP, firstMP in *; simpl in *.
        rewrite H5 in H1; assumption.
      - unfold FirstMPI, FirstMP, firstMP in *; simpl in *.
        rewrite H4 in H1; assumption.
    Qed.

    Lemma SimExtMP_outs_deqMP_child_1:
      forall msg imsgs (orqs: ORqs Msg) smsgs corq1,
        orqs@[child1Idx] = Some corq1 ->
        corq1@[upRq] = None ->
        FirstMPI imsgs (ec1, msg) ->
        SimExtMP imsgs orqs smsgs ->
        SimExtMP (deqMP ec1 imsgs) orqs (deqMP ec1 smsgs).
    Proof.
      unfold SimExtMP; intros.
      disc_rule_conds_ex.
      repeat split;
        try (do 2 (rewrite findQ_not_In_deqMP by discriminate);
             assumption).

      (* extract to a lemma? *)
      clear -H2.
      unfold deqMP.
      rewrite H2.
      change ec1 with (erq 0) in *.
      destruct (findQ (erq 0) smsgs) eqn:Hq.
      - congruence.
      - unfold findQ; mred.
    Qed.
      
    Lemma SimExtMP_outs_deqMP_child_2:
      forall msg imsgs (orqs: ORqs Msg) smsgs corq2,
        orqs@[child2Idx] = Some corq2 ->
        corq2@[upRq] = None ->
        FirstMPI imsgs (ec2, msg) ->
        SimExtMP imsgs orqs smsgs ->
        SimExtMP (deqMP ec2 imsgs) orqs (deqMP ec2 smsgs).
    Proof.
      unfold SimExtMP; intros.
      disc_rule_conds_ex.
      repeat split;
        try (do 2 (rewrite findQ_not_In_deqMP by discriminate);
             assumption).

      (* extract to a lemma? *)
      clear -H3.
      unfold deqMP.
      rewrite H3.
      change ec2 with (erq 1) in *.
      destruct (findQ (erq 1) smsgs) eqn:Hq.
      - congruence.
      - unfold findQ; mred.
    Qed.

    Lemma SimExtMP_impl_enqMP_indep:
      forall midx msg imsgs (orqs: ORqs Msg) smsgs,
        ~ In midx [ce1; ce2; ec1; ec2] ->
        SimExtMP imsgs orqs smsgs ->
        SimExtMP (enqMP midx msg imsgs) orqs smsgs.
    Proof.
      unfold SimExtMP; intros.
      disc_rule_conds_ex.
      repeat split;
        try (rewrite findQ_not_In_enqMP
              by (intro; subst; clear -H; firstorder);
             assumption).
    Qed.

    Lemma SimExtMP_impl_deqMP_indep:
      forall midx imsgs (orqs: ORqs Msg) smsgs,
        ~ In midx [ce1; ce2; ec1; ec2] ->
        SimExtMP imsgs orqs smsgs ->
        SimExtMP (deqMP midx imsgs) orqs smsgs.
    Proof.
      unfold SimExtMP; intros.
      disc_rule_conds_ex.
      repeat split;
        try (rewrite findQ_not_In_deqMP
              by (intro; subst; clear -H; firstorder);
             assumption).
    Qed.

    Lemma SimExtMP_spec_deqMP_locked_1:
      forall imsgs (orqs: ORqs Msg) smsgs porq1 norq1 rqiu1 msg,
        orqs@[child1Idx] = Some porq1 ->
        porq1@[upRq] = None -> norq1@[upRq] = Some rqiu1 ->
        FirstMPI imsgs (ec1, msg) ->
        rqiu1.(rqi_msg) = Some msg ->
        SimExtMP imsgs orqs smsgs ->
        SimExtMP (deqMP ec1 imsgs) (orqs +[child1Idx <- norq1]) smsgs.
    Proof.
      unfold SimExtMP; intros.
      disc_rule_conds_ex.
      repeat split;
        try (rewrite findQ_not_In_deqMP by discriminate;
             assumption).
      rewrite findQ_In_deqMP_FirstMP; assumption.
    Qed.

    Lemma SimExtMP_spec_deqMP_locked_2:
      forall imsgs (orqs: ORqs Msg) smsgs porq2 norq2 rqiu2 msg,
        orqs@[child2Idx] = Some porq2 ->
        porq2@[upRq] = None -> norq2@[upRq] = Some rqiu2 ->
        FirstMPI imsgs (ec2, msg) ->
        rqiu2.(rqi_msg) = Some msg ->
        SimExtMP imsgs orqs smsgs ->
        SimExtMP (deqMP ec2 imsgs) (orqs +[child2Idx <- norq2]) smsgs.
    Proof.
      unfold SimExtMP; intros.
      disc_rule_conds_ex.
      repeat split;
        try (rewrite findQ_not_In_deqMP by discriminate;
             assumption).
      rewrite findQ_In_deqMP_FirstMP; assumption.
    Qed.

    Lemma SimExtMP_spec_deqMP_unlocked_1:
      forall imsgs (orqs: ORqs Msg) smsgs porq1 rqiu1 norq1,
        orqs@[child1Idx] = Some porq1 ->
        porq1@[upRq] = Some rqiu1 -> rqiu1.(rqi_msg) <> None ->
        norq1@[upRq] = None ->
        SimExtMP imsgs orqs smsgs ->
        SimExtMP imsgs (orqs +[child1Idx <- norq1]) (deqMP ec1 smsgs).
    Proof.
      unfold SimExtMP; intros.
      disc_rule_conds_ex.
      repeat split;
        try (rewrite findQ_not_In_deqMP by discriminate;
             assumption).
      unfold deqMP.
      change ec1 with (erq 0).
      rewrite <-H3.
      destruct (rqi_msg rqiu1); [|exfalso; auto].
      simpl; unfold findQ; mred.
    Qed.

    Lemma SimExtMP_spec_deqMP_unlocked_2:
      forall imsgs (orqs: ORqs Msg) smsgs porq2 rqiu2 norq2,
        orqs@[child2Idx] = Some porq2 ->
        porq2@[upRq] = Some rqiu2 -> rqiu2.(rqi_msg) <> None ->
        norq2@[upRq] = None ->
        SimExtMP imsgs orqs smsgs ->
        SimExtMP imsgs (orqs +[child2Idx <- norq2]) (deqMP ec2 smsgs).
    Proof.
      unfold SimExtMP; intros.
      disc_rule_conds_ex.
      repeat split;
        try (rewrite findQ_not_In_deqMP by discriminate;
             assumption).
      unfold deqMP.
      change ec2 with (erq 1).
      rewrite <-H4.
      destruct (rqi_msg rqiu2); [|exfalso; auto].
      simpl; unfold findQ; mred.
    Qed.

    Lemma invalidMsgs_DirMsgsCoh:
      forall cost pc cpRq cpRs msgs,
        InvalidMsgs cost pc cpRq cpRs msgs ->
        forall cv, DirMsgsCoh cv cost pc cpRq cpRs msgs.
    Proof.
      unfold InvalidMsgs, DirMsgsCoh, DirMsgCoh; intros.
      specialize (H _ H0).
      unfold caseDec in *.
      repeat (destruct (sig_dec _ _); [exfalso; auto; fail|]).
      destruct (sig_dec _ _).
      - intros; exfalso.
        rewrite H in H1; solve_msi.
      - auto.
    Qed.

    Lemma DirMsgsCoh_child_status:
      forall cv (cost1 cost2: OState) pc cpRq cpRs msgs,
        DirMsgsCoh cv cost1 pc cpRq cpRs msgs ->
        cost2#[implStatusIdx] <= cost1#[implStatusIdx] ->
        DirMsgsCoh cv cost2 pc cpRq cpRs msgs.
    Proof.
      unfold DirMsgsCoh, DirMsgCoh; intros.
      specialize (H _ H1).
      unfold caseDec in *.
      repeat (destruct (sig_dec _ _); [auto; fail|]).
      destruct (sig_dec _ _).
      - intros; apply H; clear -H0 H2; solve_msi.
      - auto.
    Qed.

    Lemma DirMsgsCoh_no_RqI:
      forall cv (cost1 cost2: OState) pc cpRq cpRs msgs,
        DirMsgsCoh cv cost1 pc cpRq cpRs msgs ->
        (forall idm, sigOf idm = (cpRq, (MRq, msiRqI)) -> ~ InMPI msgs idm) ->
        DirMsgsCoh cv cost2 pc cpRq cpRs msgs.
    Proof.
      unfold DirMsgsCoh, DirMsgCoh; intros.
      specialize (H _ H1).
      unfold caseDec in *.
      repeat (destruct (sig_dec _ _); [auto; fail|]).
      destruct (sig_dec _ _).
      - exfalso; specialize (H0 _ e); auto.
      - auto.
    Qed.

    Lemma DirMsgsCoh_enqMP:
      forall cv cost pc cpRq cpRs msgs,
        DirMsgsCoh cv cost pc cpRq cpRs msgs ->
        forall midx msg,
          DirMsgCoh cv cost pc cpRq cpRs (midx, msg) ->
          DirMsgsCoh cv cost pc cpRq cpRs (enqMP midx msg msgs).
    Proof.
      unfold DirMsgsCoh; intros.
      apply InMP_enqMP_or in H1; destruct H1; auto.
      destruct idm as [midx' msg']; simpl in *; dest; subst.
      assumption.
    Qed.

    Definition cohMsgIds: list IdxT :=
      [msiRsS; msiDownRsS; msiRqI].
    
    Lemma DirMsgsCoh_other_msg_id_enqMP:
      forall cv cost pc cpRq cpRs msgs,
        DirMsgsCoh cv cost pc cpRq cpRs msgs ->
        forall midx msg,
          ~ In (msg_id msg) cohMsgIds ->
          DirMsgsCoh cv cost pc cpRq cpRs (enqMP midx msg msgs).
    Proof.
      unfold DirMsgsCoh; intros.
      apply InMP_enqMP_or in H1; destruct H1; auto.
      destruct idm as [midx' msg']; simpl in *; dest; subst.
      destruct msg as [mid mty mval]; simpl in H0.
      red; cbv [sigOf idOf valOf fst snd msg_id msg_type].
      unfold caseDec.
      repeat (find_if_inside; [inv e; exfalso; intuition idtac|]).
      auto.
    Qed.

    Lemma DirMsgsCoh_other_msg_id_enqMsgs:
      forall cv cost pc cpRq cpRs msgs,
        DirMsgsCoh cv cost pc cpRq cpRs msgs ->
        forall eins,
          DisjList (map (fun idm => msg_id (valOf idm)) eins) cohMsgIds ->
          DirMsgsCoh cv cost pc cpRq cpRs (enqMsgs eins msgs).
    Proof.
      intros.
      generalize dependent msgs.
      induction eins as [|ein eins]; simpl; intros; [assumption|].
      destruct ein as [midx msg]; simpl in *.
      apply DisjList_cons in H0; dest.
      eapply IHeins; eauto.
      apply DirMsgsCoh_other_msg_id_enqMP; auto.
    Qed.

    Lemma DirMsgsCoh_other_midx_enqMP:
      forall cv cost pc cpRq cpRs msgs,
        DirMsgsCoh cv cost pc cpRq cpRs msgs ->
        forall midx msg,
          ~ In midx [pc; cpRq; cpRs] ->
          DirMsgsCoh cv cost pc cpRq cpRs (enqMP midx msg msgs).
    Proof.
      unfold DirMsgsCoh; intros.
      apply InMP_enqMP_or in H1; destruct H1; auto.
      destruct idm as [midx' msg']; simpl in *; dest; subst.
      destruct msg as [mid mty mval].
      red; cbv [sigOf idOf valOf fst snd msg_id msg_type].
      unfold caseDec.
      repeat (find_if_inside; [inv e; exfalso; intuition idtac|]).
      auto.
    Qed.

    Lemma DirMsgsCoh_other_midx_enqMsgs:
      forall cv cost pc cpRq cpRs msgs,
        DirMsgsCoh cv cost pc cpRq cpRs msgs ->
        forall eins,
          DisjList (idsOf eins) [pc; cpRq; cpRs] ->
          DirMsgsCoh cv cost pc cpRq cpRs (enqMsgs eins msgs).
    Proof.
      intros.
      generalize dependent msgs.
      induction eins as [|ein eins]; simpl; intros; [assumption|].
      destruct ein as [midx msg]; simpl in *.
      apply DisjList_cons in H0; dest.
      eapply IHeins; eauto.
      apply DirMsgsCoh_other_midx_enqMP; auto.
    Qed.

    Lemma DirMsgsCoh_deqMP:
      forall cv cost pc cpRq cpRs msgs,
        DirMsgsCoh cv cost pc cpRq cpRs msgs ->
        forall midx,
          DirMsgsCoh cv cost pc cpRq cpRs (deqMP midx msgs).
    Proof.
      unfold DirMsgsCoh; intros.
      apply InMP_deqMP in H0; auto.
    Qed.

    Lemma DirMsgsCoh_deqMsgs:
      forall cv cost pc cpRq cpRs msgs,
        DirMsgsCoh cv cost pc cpRq cpRs msgs ->
        forall minds,
          DirMsgsCoh cv cost pc cpRq cpRs (deqMsgs minds msgs).
    Proof.
      unfold DirMsgsCoh; intros.
      apply InMP_deqMsgs in H0; auto.
    Qed.

    Definition cohMinds: list IdxT :=
      [pc1; pc2; c1pRs; c2pRs; c1pRq; c2pRq].

    Lemma SimState_impl_other_midx_enqMsgs:
      forall ioss iorqs imsgs sst,
        SimState {| bst_oss := ioss; bst_orqs := iorqs; bst_msgs := imsgs |} sst ->
        forall nmsgs,
          DisjList (idsOf nmsgs) cohMinds ->
          SimState {| bst_oss := ioss; bst_orqs := iorqs;
                      bst_msgs := enqMsgs nmsgs imsgs |} sst.
    Proof.
      intros.
      inv H.
      apply SimStateIntro with (cv:= cv); [assumption|].
      clear H1.
      red in H2; red; simpl in *.
      disc_rule_conds_ex.
      repeat split; intuition.
      - apply DirMsgsCoh_other_midx_enqMsgs; auto.
        eapply DisjList_comm, DisjList_SubList;
          [|apply DisjList_comm; eassumption].
        solve_SubList.
      - apply DirMsgsCoh_other_midx_enqMsgs; auto.
        eapply DisjList_comm, DisjList_SubList;
          [|apply DisjList_comm; eassumption].
        solve_SubList.
    Qed.

    Lemma SimState_spec_enqMsgs:
      forall ist soss sorqs smsgs,
        SimState ist {| bst_oss := soss; bst_orqs := sorqs; bst_msgs := smsgs |} ->
        forall nmsgs,
          SimState ist {| bst_oss := soss; bst_orqs := sorqs;
                          bst_msgs := enqMsgs nmsgs smsgs |}.
    Proof.
      intros; inv H; econstructor; eauto.
    Qed.

    Lemma SimState_impl_deqMsgs:
      forall ioss iorqs imsgs sst,
        SimState {| bst_oss := ioss; bst_orqs := iorqs; bst_msgs := imsgs |} sst ->
        forall minds,
          SimState {| bst_oss := ioss; bst_orqs := iorqs;
                      bst_msgs := deqMsgs minds imsgs |} sst.
    Proof.
      intros.
      inv H.
      apply SimStateIntro with (cv:= cv); [assumption|].
      clear H0.
      red in H1; red; simpl in *.
      disc_rule_conds_ex.
      repeat split; intuition.
      - apply DirMsgsCoh_deqMsgs; assumption.
      - apply DirMsgsCoh_deqMsgs; assumption.
    Qed.

    Lemma SimState_spec_deqMsgs:
      forall ist soss sorqs smsgs,
        SimState ist {| bst_oss := soss; bst_orqs := sorqs; bst_msgs := smsgs |} ->
        forall minds,
          SimState ist {| bst_oss := soss; bst_orqs := sorqs;
                          bst_msgs := deqMsgs minds smsgs |}.
    Proof.
      intros; inv H; econstructor; eauto.
    Qed.

    Ltac spec_constr_step_get_FirstMPI :=
      repeat constructor;
      match goal with
      | [H: SimExtMP _ _ _ |- _] => red in H; disc_rule_conds_const; dest
      end;
      eapply findQ_eq_FirstMPI; eauto.

    Ltac spec_constr_step_get_ValidMsgs :=
      clear; split;
      [simpl; apply SubList_cons; [|apply SubList_nil];
       simpl; tauto
      |repeat constructor; intro; dest_in].

    Ltac spec_constr_step_get ecmidx :=
      match goal with
      | [H: msg_id ?msg = Spec.getRq |- _] =>
        eapply SmInt with (obj:= specObj 1) (ins:= [(ecmidx, msg)]);
        try reflexivity;
        [left; reflexivity (* object in *)
        |simpl; tauto (* rule in *)
        |eassumption
        |eassumption
        |spec_constr_step_get_FirstMPI
        |spec_constr_step_get_ValidMsgs
        |solve_rule_conds_ex (* rule_precond *)
        |spec_constr_step_get_ValidMsgs
        |solve_DisjList idx_dec]
      end.

    Ltac spec_constr_step_set ecmidx :=
      match goal with
      | [H: msg_id ?msg = Spec.setRq |- _] =>
        eapply SmInt with (obj:= specObj 1) (ins:= [(ecmidx, msg)]);
        try reflexivity;
        [left; reflexivity (* object in *)
        |simpl; tauto (* rule in *)
        |eassumption
        |eassumption
        |spec_constr_step_get_FirstMPI
        |spec_constr_step_get_ValidMsgs
        |solve_rule_conds_ex (* rule_precond *)
        |spec_constr_step_get_ValidMsgs
        |solve_DisjList idx_dec]
      end.

    Ltac spec_constr_step_evict ecmidx :=
      match goal with
      | [H: msg_id ?msg = Spec.evictRq |- _] =>
        eapply SmInt with (obj:= specObj 1) (ins:= [(ecmidx, msg)]);
        try reflexivity;
        [left; reflexivity (* object in *)
        |simpl; tauto (* rule in *)
        |eassumption
        |eassumption
        |spec_constr_step_get_FirstMPI
        |spec_constr_step_get_ValidMsgs
        |solve_rule_conds_ex (* rule_precond *)
        |spec_constr_step_get_ValidMsgs
        |solve_DisjList idx_dec]
      end.

    Ltac spec_case_get cidx ecmidx :=
      eexists (RlblInt 0 (rule_idx (specGetRq cidx)) _ _); eexists;
      repeat ssplit;
      [reflexivity
      |spec_constr_step_get ecmidx
      |].

    Ltac spec_case_set cidx ecmidx :=
      eexists (RlblInt 0 (rule_idx (specSetRq cidx)) _ _); eexists;
      repeat ssplit;
      [reflexivity
      |spec_constr_step_set ecmidx
      |].
    
    Ltac spec_case_silent :=
      idtac; exists (RlblEmpty _); eexists;
      repeat ssplit;
      [reflexivity
      |econstructor
      |].

    Ltac spec_case_evict cidx ecmidx :=
      eexists (RlblInt 0 (rule_idx (specEvictRq cidx)) _ _); eexists;
      repeat ssplit;
      [reflexivity
      |spec_constr_step_evict ecmidx
      |].

    Ltac solve_sim_ext_mp :=
      repeat
        (match goal with
         | [ |- SimExtMP _ (?m +[?k <- ?v]) _ ] =>
           apply SimExtMP_orqs with (orqs1:= m); [|findeq; fail|findeq; fail]
         | [ |- SimExtMP (enqMP _ _ _) _ (enqMP _ _ _) ] =>
           apply SimExtMP_enqMP
         | [ |- SimExtMP (deqMP ec1 _) _ (deqMP ec1 _) ] =>
           eapply SimExtMP_outs_deqMP_child_1; eauto; fail
         | [ |- SimExtMP (deqMP ec2 _) _ (deqMP ec2 _) ] =>
           eapply SimExtMP_outs_deqMP_child_2; eauto; fail
         | [ |- SimExtMP (enqMP _ _ _) _ _ ] =>
           apply SimExtMP_impl_enqMP_indep; [solve_not_in; fail|]
         | [ |- SimExtMP (deqMP ec1 _) _ _ ] =>
           eapply SimExtMP_spec_deqMP_locked_1; eauto; [mred|reflexivity]; fail
         | [ |- SimExtMP (deqMP ec2 _) _ _ ] =>
           eapply SimExtMP_spec_deqMP_locked_2; eauto; [mred|reflexivity]; fail
         | [ |- SimExtMP (deqMP _ _) _ _ ] =>
           apply SimExtMP_impl_deqMP_indep; [solve_not_in; fail|]
         | [ |- SimExtMP _ _ (deqMP ec1 _) ] =>
           eapply SimExtMP_spec_deqMP_unlocked_1; eauto; [congruence|mred]; fail
         | [ |- SimExtMP _ _ (deqMP ec2 _) ] =>
           eapply SimExtMP_spec_deqMP_unlocked_2; eauto; [congruence|mred]; fail
         end; try assumption).

    Ltac solve_sim_obj :=
      repeat
        match goal with
        | [ |- SimMSI _ _] => red; simpl; split
        | [ |- SimExtMP _ _ _ ] => solve_sim_ext_mp
        | [sost: OState SpecOStateIfc |- SimState _ _] =>
          eapply SimStateIntro with (cv:= fst sost)
        | [ |- SpecStateCoh _ _] => solve_rule_conds_ex; solve_msi
        | [ |- ImplStateCoh _ _] => red; simpl; solve_rule_conds_ex
        end.

    Ltac disc_DirMsgsCoh_by_FirstMP Hd Hf :=
      specialize (Hd _ (FirstMP_InMP Hf));
      red in Hd; unfold sigOf, valOf, snd in Hd;
      match type of Hf with
      | FirstMPI _ (_, ?msg) =>
        match goal with
        | [H1: msg_id ?msg = _, H2: msg_type ?msg = _ |- _] =>
          rewrite H1, H2 in Hd; simpl in Hd
        end
      end.

    Lemma simMsiSv_sim_silent:
      forall ist sst1,
        SimMSI ist sst1 ->
        exists slbl sst2,
          getLabel (RlblEmpty Msg) = getLabel slbl /\
          step_m spec sst1 slbl sst2 /\ SimMSI ist sst2.
    Proof.
      simpl; intros.
      exists (RlblEmpty _); eexists.
      repeat ssplit; eauto.
      constructor.
    Qed.

    Lemma simMsiSv_sim_ext_in:
      forall oss orqs msgs sst1,
        SimMSI {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} sst1 ->
        forall eins,
          eins <> nil -> ValidMsgsExtIn impl eins ->
          exists slbl sst2,
            getLabel (RlblIns eins) = getLabel slbl /\
            step_m spec sst1 slbl sst2 /\
            SimMSI {| bst_oss := oss;
                      bst_orqs := orqs;
                      bst_msgs := enqMsgs eins msgs |} sst2.
    Proof.
      destruct sst1 as [soss1 sorqs1 smsgs1]; simpl; intros.
      red in H; simpl in *; dest.
      exists (RlblIns eins); eexists.
      repeat ssplit.
      + reflexivity.
      + eapply SmIns; eauto.
      + split.
        * apply SimState_spec_enqMsgs.
          apply SimState_impl_other_midx_enqMsgs; [assumption|].
          destruct H1.
          eapply DisjList_SubList; [eassumption|].
          solve_DisjList idx_dec.
        * apply SimExtMP_enqMsgs; auto.
          apply H1.
    Qed.

    Lemma simMsiSv_sim_ext_out:
      forall oss orqs msgs sst1,
        SimMSI {| bst_oss := oss; bst_orqs := orqs; bst_msgs := msgs |} sst1 ->
        forall eouts: list (Id Msg),
          eouts <> nil ->
          Forall (FirstMPI msgs) eouts ->
          ValidMsgsExtOut impl eouts ->
          exists slbl sst2,
            getLabel (RlblOuts eouts) = getLabel slbl /\
            step_m spec sst1 slbl sst2 /\
            SimMSI {| bst_oss := oss;
                      bst_orqs := orqs;
                      bst_msgs := deqMsgs (idsOf eouts) msgs |} sst2.
    Proof.
      destruct sst1 as [soss1 sorqs1 smsgs1]; simpl; intros.
      red in H; simpl in *; dest.
      exists (RlblOuts eouts); eexists.
      repeat ssplit.
      + reflexivity.
      + eapply SmOuts with (msgs0:= smsgs1); eauto.
        eapply SimExtMP_ext_outs_FirstMPI; eauto.
      + split.
        * apply SimState_spec_deqMsgs.
          apply SimState_impl_deqMsgs.
          assumption.
        * apply SimExtMP_ext_outs_deqMsgs; auto.
    Qed.

    Definition ImplInvEx (st: MState) :=
      ImplInv st /\ ImplInvB st.

    Hint Unfold ImplInvEx ImplInv ImplInvB: RuleConds.

    Lemma simMsiSv_sim:
      InvSim step_m step_m ImplInvEx SimMSI impl spec.
    Proof.
      red; intros.

      pose proof (footprints_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys H) as Hftinv.
      pose proof (upLockInv_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree H) as Hpulinv.
      pose proof (upLockInv_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys
                    msiSv_impl_RqRsDTree
                    (reachable_steps H (steps_singleton H2))) as Hnulinv.

      inv H2;
        [apply simMsiSv_sim_silent; assumption
        |apply simMsiSv_sim_ext_in; assumption
        |apply simMsiSv_sim_ext_out; assumption
        |].

      destruct sst1 as [soss1 sorqs1 smsgs1].
      destruct H0; simpl in H0, H2; simpl.
      inv H0.
      red in H15; simpl in H15.
      destruct (oss@[parentIdx]) as [post|] eqn:Hpost; simpl in *; [|exfalso; auto].
      destruct (oss@[child1Idx]) as [cost1|] eqn:Hcost1; simpl in *; [|exfalso; auto].
      destruct (oss@[child2Idx]) as [cost2|] eqn:Hcost2; simpl in *; [|exfalso; auto].
      destruct (orqs@[child1Idx]) as [corq1|] eqn:Hcorq1; simpl in *; [|exfalso; auto].
      destruct (orqs@[child2Idx]) as [corq2|] eqn:Hcorq2; simpl in *; [|exfalso; auto].
      red in H6; simpl in H6.
      destruct (soss1@[specIdx]) as [sost|] eqn:Hsost; simpl in *; [|exfalso; auto].
      destruct (sorqs1@[specIdx]) as [sorq|] eqn:Hsorq; simpl in *; [|exfalso; auto].
      dest; subst.
      
      destruct H4 as [|[|[|]]];
        try (exfalso; auto; fail); subst; dest_in.

      (*! Cases for [child1] *)

      - (** [childGetRqImm] *)
        disc_rule_conds_ex.
        spec_case_get 0 ec1.

        assert (pos#[implValueIdx] = fst sost).
        { solve_rule_conds_ex.
          apply H15; [|auto].
          clear -H3 H20; solve_msi.
        }
        simpl in H6; rewrite H6 in *.
        
        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      - (** [childGetRqS] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      - (** [childGetRsS] *)
        disc_rule_conds_ex.
        spec_case_get 0 ec1;
          [unfold FirstMPI, FirstMP, firstMP;
           simpl; change ec1 with (erq 0);
           rewrite <-H2; reflexivity|].

        get_lock_minds child1Idx.
        clear Hnulinv.
        get_lock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
        disc_rule_conds_const.

        assert (msg_value rmsg = fst sost)
          by (disc_DirMsgsCoh_by_FirstMP H15 H55; assumption).
        rewrite H6 in *.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in]. 
              apply DirMsgsCoh_deqMP.
              eapply DirMsgsCoh_no_RqI; eauto.
              intros; intro Hx.
              destruct idm as [midx rq]; inv H62.
              exfalso_uplock_rq_rs parentIdx c1pRq pc1.
            }
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      - (** [childDownRqS] *)
        disc_rule_conds_ex.
        spec_case_silent.
        
        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_enqMP.
              { apply DirMsgsCoh_deqMP.
                eapply DirMsgsCoh_child_status; eauto.
              }
              { cbn; congruence. }
            }
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      - (** [childSetRqImm] *)
        disc_rule_conds_ex.
        spec_case_set 0 ec1.

        rewrite H20 in H1.
        disc_rule_conds_ex.
              
        red; simpl; split.
        + eapply SimStateIntro with (cv:= msg_value rmsg).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac; try solve_msi_false.
            apply invalidMsgs_DirMsgsCoh.
            apply H29; auto.
            clear -H20; solve_msi.
        + solve_sim_ext_mp.

      - (** [childSetRqM] *)
        disc_rule_conds_ex.
        spec_case_silent.
        
        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.
          
      - (** [childSetRsM] *)
        disc_rule_conds_ex.
        spec_case_set 0 ec1;
          [unfold FirstMPI, FirstMP, firstMP;
           simpl; change ec1 with (erq 0);
           rewrite <-H2; reflexivity|].

        clear Hnulinv.
        get_lock_minds child1Idx.
        disc_rule_conds_ex.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= msg_value msg).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { solve_msi_false. }
            { apply invalidMsgs_DirMsgsCoh.
              apply H29; auto.
            }
            { solve_msi_false. }
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              apply invalidMsgs_DirMsgsCoh; assumption.
            }
        + solve_sim_ext_mp.

      - (** [childDownRqI] *)
        disc_rule_conds_ex.
        spec_case_silent.
        
        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              eapply DirMsgsCoh_child_status; eauto.
              simpl; clear; solve_msi.
            }
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      - (** [childEvictRqI] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_enqMP.
              { apply DirMsgsCoh_deqMP; assumption. }
              { cbn; intros; intuition. }
            }
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      - (** [childEvictRsI] *)
        disc_rule_conds_ex.
        spec_case_evict 0 ec1;
          [unfold FirstMPI, FirstMP, firstMP;
           simpl; change ec1 with (erq 0);
           rewrite <-H2; reflexivity|].

        get_lock_minds child1Idx.
        disc_rule_conds_ex.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { solve_msi_false. }
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              eapply DirMsgsCoh_child_status; eauto.
              simpl; clear; solve_msi.
            }
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      (*! Cases for [child2] *)

      - (** [childGetRqImm] *)
        disc_rule_conds_ex.
        spec_case_get 1 ec2.

        assert (pos#[implValueIdx] = fst sost).
        { solve_rule_conds_ex.
          apply H16; [|auto].
          clear -H34 H20; solve_msi.
        }
        simpl in H6; rewrite H6 in *.
        
        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      - (** [childGetRqS] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      - (** [childGetRsS] *)
        disc_rule_conds_ex.
        spec_case_get 1 ec2;
          [unfold FirstMPI, FirstMP, firstMP;
           simpl; change ec2 with (erq 1);
           rewrite <-H8; reflexivity|].

        get_lock_minds child2Idx.
        clear Hnulinv.
        get_lock_inv (child child2Idx ec2 ce2 c2pRq c2pRs pc2) impl.
        disc_rule_conds_const.

        assert (msg_value rmsg = fst sost)
          by (disc_DirMsgsCoh_by_FirstMP H16 H55; congruence).
        rewrite H6 in *.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in]. 
              apply DirMsgsCoh_deqMP.
              eapply DirMsgsCoh_no_RqI; eauto.
              intros; intro Hx.
              destruct idm as [midx rq]; inv H62.
              exfalso_uplock_rq_rs parentIdx c2pRq pc2.
            }
        + solve_sim_ext_mp.

      - (** [childDownRqS] *)
        disc_rule_conds_ex.
        spec_case_silent.
        
        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_enqMP.
              { apply DirMsgsCoh_deqMP.
                eapply DirMsgsCoh_child_status; eauto.
              }
              { cbn; congruence. }
            }
        + solve_sim_ext_mp.

      - (** [childSetRqImm] *)
        disc_rule_conds_ex.
        spec_case_set 1 ec2.

        rewrite H20 in H52.
        disc_rule_conds_ex.
              
        red; simpl; split.
        + eapply SimStateIntro with (cv:= msg_value rmsg).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac; try solve_msi_false.
            apply invalidMsgs_DirMsgsCoh.
            apply H30; auto.
            clear -H20; solve_msi.
        + solve_sim_ext_mp.

      - (** [childSetRqM] *)
        disc_rule_conds_ex.
        spec_case_silent.
        
        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.
          
      - (** [childSetRsM] *)
        disc_rule_conds_ex.
        spec_case_set 1 ec2;
          [unfold FirstMPI, FirstMP, firstMP;
           simpl; change ec2 with (erq 1);
           rewrite <-H8; reflexivity|].

        clear Hnulinv.
        get_lock_minds child2Idx.
        disc_rule_conds_ex.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= msg_value msg).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { solve_msi_false. }
            { solve_msi_false. }
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              apply invalidMsgs_DirMsgsCoh; assumption.
            }
            { apply invalidMsgs_DirMsgsCoh.
              apply H30; auto.
            }
        + solve_sim_ext_mp.

      - (** [childDownRqI] *)
        disc_rule_conds_ex.
        spec_case_silent.
        
        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              eapply DirMsgsCoh_child_status; eauto.
              simpl; clear; solve_msi.
            }
        + solve_sim_ext_mp.

      - (** [childEvictRqI] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_enqMP.
              { apply DirMsgsCoh_deqMP; assumption. }
              { cbn; intros; intuition. }
            }
        + solve_sim_ext_mp.

      - (** [childEvictRsI] *)
        disc_rule_conds_ex.
        spec_case_evict 1 ec2;
          [unfold FirstMPI, FirstMP, firstMP;
           simpl; change ec2 with (erq 1);
           rewrite <-H8; reflexivity|].

        get_lock_minds child2Idx.
        disc_rule_conds_ex.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { solve_msi_false. }
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              eapply DirMsgsCoh_child_status; eauto.
              simpl; clear; solve_msi.
            }
        + solve_sim_ext_mp.

      (*! Cases for [parent] with [child1] *)

      - (** [parentGetRqImm] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            destruct (Compare_dec.le_gt_dec msiM (fst (snd post))).
            { disc_rule_conds_ex.
              intuition idtac.
              { destruct H48.
                { exfalso; simpl in *; solve_msi_false. }
                { destruct H48 as [[midx msg] [? ?]]; inv H62.
                  clear Hpulinv.
                  get_lock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
                  disc_rule_conds_const.
                  exfalso.
                  exfalso_uplock_rs_two
                    parentIdx pc1 msg
                    {| msg_id:= msiRsS;
                       msg_type:= MRs;
                       msg_value:= fst post |}.
                }
              }
              { apply DirMsgsCoh_enqMP.
                { apply DirMsgsCoh_deqMP.
                  apply invalidMsgs_DirMsgsCoh; assumption.
                }
                { red; simpl; congruence. }
              }
              { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
                apply DirMsgsCoh_deqMP; assumption.
              }
            }
            
            { assert (fst (snd post) = msiS) by (clear -g H20; solve_msi).
              disc_rule_conds_ex.
              destruct (eq_nat_dec (fst (fst (snd (snd post)))) msiS).
              { specialize (H15 ltac:(clear -e; solve_msi)); dest.
                intuition idtac.
                { apply DirMsgsCoh_enqMP.
                  { apply DirMsgsCoh_deqMP; assumption. }
                  { red; simpl; congruence. }
                }
                { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
                  apply DirMsgsCoh_deqMP; assumption.
                }
              }
              { assert (fst (fst (snd (snd post))) = msiI)
                  by (clear -H25 n; solve_msi).
                disc_rule_conds_ex.
                intuition idtac.
                { destruct H48.
                  { exfalso; simpl in *; solve_msi_false. }
                  { destruct H48 as [[midx msg] [? ?]]; inv H62.
                    clear Hpulinv.
                    get_lock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
                    disc_rule_conds_const.
                    exfalso.
                    exfalso_uplock_rs_two
                      parentIdx pc1 msg
                      {| msg_id:= msiRsS;
                         msg_type:= MRs;
                         msg_value:= fst post |}.
                  }
                }
                { apply DirMsgsCoh_enqMP.
                  { apply DirMsgsCoh_deqMP.
                    apply invalidMsgs_DirMsgsCoh; assumption.
                  }
                  { red; simpl; congruence. }
                }
                { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
                  apply DirMsgsCoh_deqMP; assumption.
                }
              }
            }
        + solve_sim_ext_mp.

      - (** [parentGetDownRqS] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      - (** [parentSetRqImm] *)
        disc_rule_conds_ex.
        spec_case_silent.

        (* simplify [getDir] *)
        unfold getDir in *; simpl in *.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            destruct (Compare_dec.le_gt_dec msiS (fst (fst (snd (snd post))))).
            { disc_rule_conds_ex.
              intuition idtac; try solve_msi_false.
              apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { assert (fst (fst (snd (snd post))) = msiI) by (clear -g; solve_msi).
              disc_rule_conds_ex.
              intuition idtac; try solve_msi_false.
              { destruct H48.
                { exfalso; simpl in *; solve_msi_false. }
                { destruct H48 as [[midx msg] [? ?]]; inv H63.
                  clear Hpulinv.
                  get_lock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
                  disc_rule_conds_const.
                  exfalso.
                  exfalso_uplock_rs_two
                    parentIdx pc1 msg
                    {| msg_id:= msiRsM;
                       msg_type:= MRs;
                       msg_value:= O |}.
                }
              }
              { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
                apply DirMsgsCoh_deqMP.
                apply invalidMsgs_DirMsgsCoh.
                assumption.
              }
            }            
        + solve_sim_ext_mp.

      - (** [parentSetDownRqI] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      - (** [parentGetDownRsS] *)
        disc_rule_conds_ex.
        spec_case_silent.

        inv H60.
        unfold setDir in *; simpl in *.

        (* Discharge the downlock invariant *)
        specialize (H37 eq_refl); dest.
        disc_rule_conds_ex.

        (* To get [DirMsgsCoh (fst sost) cost2 ..]  *)
        specialize (H16 ltac:(clear -H43; solve_msi)); dest.
        pose proof H59.
        disc_DirMsgsCoh_by_FirstMP H60 H54.
        rewrite H60 in *.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { destruct H47.
              { exfalso; simpl in *; solve_msi_false. }
              { destruct H47 as [[midx rs] [? ?]]; inv H65.
                clear Hpulinv.
                get_lock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
                disc_rule_conds_const.
                exfalso.
                exfalso_uplock_rs_two
                  parentIdx pc1 rs
                  {| msg_id:= msiRsS;
                     msg_type:= MRs;
                     msg_value:= fst sost |}.
              }
            }
            { apply DirMsgsCoh_enqMP.
              { apply DirMsgsCoh_deqMP.
                apply invalidMsgs_DirMsgsCoh; assumption.
              }
              { reflexivity. }
            }
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP; assumption.
            }
        + solve_sim_ext_mp.

      - (** [parentSetDownRsI] *)
        disc_rule_conds_ex.
        spec_case_silent.

        inv H61.
        unfold setDir in *; simpl in *.

        specialize (H57 eq_refl).
        disc_rule_conds_ex.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            destruct (Compare_dec.le_gt_dec msiS (fst (fst (snd (snd post))))).
            { disc_rule_conds_ex.
              intuition idtac; try solve_msi_false.
              apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { assert (fst (fst (snd (snd post))) = msiI) by (clear -g; solve_msi).
              disc_rule_conds_ex.
              intuition idtac; try solve_msi_false.
              { destruct H47.
                { exfalso; simpl in *; solve_msi_false. }
                { destruct H47 as [[midx rs] [? ?]]; inv H65.
                  clear Hpulinv.
                  get_lock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
                  disc_rule_conds_const.
                  exfalso.
                  exfalso_uplock_rs_two
                    parentIdx pc1 rs
                    {| msg_id:= msiRsM;
                       msg_type:= MRs;
                       msg_value:= O |}.
                }
              }
              { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
                apply DirMsgsCoh_deqMP.
                apply invalidMsgs_DirMsgsCoh.
                assumption.
              }
            }
        + solve_sim_ext_mp.

      - (** [parentEvictRqImmI] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      - (** [parentEvictRqImmS] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { solve_msi_false. }
            { solve_msi_false. }
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      - (** [parentEvictRqImmLastS] *)
        disc_rule_conds_ex.
        spec_case_silent.

        (* simplify [getDir] *)
        unfold getDir in *; simpl in *.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac; try solve_msi_false.
            solve_rule_conds_ex.
            apply H0; rewrite H5; auto.
        + solve_sim_ext_mp.
          
      - (** [parentEvictRqImmM] *)
        disc_rule_conds_ex.
        spec_case_silent.

        (* simplify [getDir] *)
        unfold getDir in *; simpl in *.

        (* discharging [ImplStateInv] *)
        assert (msg_value rmsg = fst sost).
        { specialize (H15 ltac:(clear -H20; solve_msi)); dest.
          disc_DirMsgsCoh_by_FirstMP H15 H56.
          assert (msiM <= fst (snd cost1)).
          { apply H51; auto.
            { rewrite H20; auto. }
            { exists (c1pRq, rmsg); split.
              { apply FirstMP_InMP; assumption. }
              { unfold sigOf; simpl.
                rewrite H55, H9; reflexivity.
              }
            }
          }
          specialize (H15 ltac:(clear -H17; solve_msi)).
          congruence.
        }
        subst.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac; try solve_msi_false.
            apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
            apply DirMsgsCoh_deqMP.
            assumption.
        + solve_sim_ext_mp.

      (*! Cases for [parent] with [child2] *)

      - (** [parentGetRqImm] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            destruct (Compare_dec.le_gt_dec msiM (fst (snd post))).
            { disc_rule_conds_ex.
              intuition idtac.
              { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
                apply DirMsgsCoh_deqMP; assumption.
              }
              { destruct H49.
                { exfalso; simpl in *; solve_msi_false. }
                { destruct H49 as [[midx msg] [? ?]]; inv H62.
                  clear Hpulinv.
                  get_lock_inv (child child2Idx ec2 ce2 c2pRq c2pRs pc2) impl.
                  disc_rule_conds_const.
                  exfalso.
                  exfalso_uplock_rs_two
                    parentIdx pc2 msg
                    {| msg_id:= msiRsS;
                       msg_type:= MRs;
                       msg_value:= fst post |}.
                }
              }
              { apply DirMsgsCoh_enqMP.
                { apply DirMsgsCoh_deqMP.
                  apply invalidMsgs_DirMsgsCoh; assumption.
                }
                { red; simpl; congruence. }
              }
            }
            
            { assert (fst (snd post) = msiS) by (clear -g H20; solve_msi).
              disc_rule_conds_ex.
              destruct (eq_nat_dec (snd (fst (snd (snd post)))) msiS).
              { specialize (H16 ltac:(clear -e; solve_msi)); dest.
                intuition idtac.
                { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
                  apply DirMsgsCoh_deqMP; assumption.
                }
                { apply DirMsgsCoh_enqMP.
                  { apply DirMsgsCoh_deqMP; assumption. }
                  { red; simpl; congruence. }
                }
              }
              { assert (snd (fst (snd (snd post))) = msiI)
                  by (clear -H42 n; solve_msi).
                disc_rule_conds_ex.
                intuition idtac.
                { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
                  apply DirMsgsCoh_deqMP; assumption.
                }
                { destruct H49.
                  { exfalso; simpl in *; solve_msi_false. }
                  { destruct H49 as [[midx msg] [? ?]]; inv H62.
                    clear Hpulinv.
                    get_lock_inv (child child2Idx ec2 ce2 c2pRq c2pRs pc2) impl.
                    disc_rule_conds_const.
                    exfalso.
                    exfalso_uplock_rs_two
                      parentIdx pc2 msg
                      {| msg_id:= msiRsS;
                         msg_type:= MRs;
                         msg_value:= fst post |}.
                  }
                }
                { apply DirMsgsCoh_enqMP.
                  { apply DirMsgsCoh_deqMP.
                    apply invalidMsgs_DirMsgsCoh; assumption.
                  }
                  { red; simpl; congruence. }
                }
              }
            }
        + solve_sim_ext_mp.

      - (** [parentGetDownRqS] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      - (** [parentSetRqImm] *)
        disc_rule_conds_ex.
        spec_case_silent.

        (* simplify [getDir] *)
        unfold getDir in *; simpl in *.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            destruct (Compare_dec.le_gt_dec msiS (snd (fst (snd (snd post))))).
            { disc_rule_conds_ex.
              intuition idtac; try solve_msi_false.
              apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { assert (snd (fst (snd (snd post))) = msiI) by (clear -g; solve_msi).
              disc_rule_conds_ex.
              intuition idtac; try solve_msi_false.
              { destruct H49.
                { exfalso; simpl in *; solve_msi_false. }
                { destruct H49 as [[midx msg] [? ?]]; inv H63.
                  clear Hpulinv.
                  get_lock_inv (child child2Idx ec2 ce2 c2pRq c2pRs pc2) impl.
                  disc_rule_conds_const.
                  exfalso.
                  exfalso_uplock_rs_two
                    parentIdx pc2 msg
                    {| msg_id:= msiRsM;
                       msg_type:= MRs;
                       msg_value:= O |}.
                }
              }
              { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
                apply DirMsgsCoh_deqMP.
                apply invalidMsgs_DirMsgsCoh.
                assumption.
              }
            }            
        + solve_sim_ext_mp.

      - (** [parentSetDownRqI] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      - (** [parentGetDownRsS] *)
        disc_rule_conds_ex.
        spec_case_silent.

        inv H60.
        unfold setDir in *; simpl in *.

        (* Discharge the downlock invariant *)
        specialize (H24 eq_refl); dest.
        disc_rule_conds_ex.

        (* To get [DirMsgsCoh (fst sost) cost1 ..]  *)
        specialize (H15 ltac:(clear -H44; solve_msi)); dest.
        pose proof H59.
        disc_DirMsgsCoh_by_FirstMP H60 H54.
        rewrite H60 in *.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_midx_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP; assumption.
            }
            { destruct H48.
              { exfalso; simpl in *; solve_msi_false. }
              { destruct H48 as [[midx rs] [? ?]]; inv H65.
                clear Hpulinv.
                get_lock_inv (child child2Idx ec2 ce2 c2pRq c2pRs pc2) impl.
                disc_rule_conds_const.
                exfalso.
                exfalso_uplock_rs_two
                  parentIdx pc2 rs
                  {| msg_id:= msiRsS;
                     msg_type:= MRs;
                     msg_value:= fst sost |}.
              }
            }
            { apply DirMsgsCoh_enqMP.
              { apply DirMsgsCoh_deqMP.
                apply invalidMsgs_DirMsgsCoh; assumption.
              }
              { reflexivity. }
            }
        + solve_sim_ext_mp.

      - (** [parentSetDownRsI] *)
        disc_rule_conds_ex.
        spec_case_silent.

        inv H61.
        unfold setDir in *; simpl in *.

        specialize (H37 eq_refl).
        disc_rule_conds_ex.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            destruct (Compare_dec.le_gt_dec msiS (snd (fst (snd (snd post))))).
            { disc_rule_conds_ex.
              intuition idtac; try solve_msi_false.
              apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { assert (snd (fst (snd (snd post))) = msiI) by (clear -g; solve_msi).
              disc_rule_conds_ex.
              intuition idtac; try solve_msi_false.
              { destruct H48.
                { exfalso; simpl in *; solve_msi_false. }
                { destruct H48 as [[midx rs] [? ?]]; inv H64.
                  clear Hpulinv.
                  get_lock_inv (child child2Idx ec2 ce2 c2pRq c2pRs pc2) impl.
                  disc_rule_conds_const.
                  exfalso.
                  exfalso_uplock_rs_two
                    parentIdx pc2 rs
                    {| msg_id:= msiRsM;
                       msg_type:= MRs;
                       msg_value:= O |}.
                }
              }
              { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
                apply DirMsgsCoh_deqMP.
                apply invalidMsgs_DirMsgsCoh.
                assumption.
              }
            }
        + solve_sim_ext_mp.

      - (** [parentEvictRqImmI] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
        + solve_sim_ext_mp.

      - (** [parentEvictRqImmS] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
              apply DirMsgsCoh_deqMP.
              assumption.
            }
            { solve_msi_false. }
            { solve_msi_false. }
        + solve_sim_ext_mp.

      - (** [parentEvictRqImmLastS] *)
        disc_rule_conds_ex.
        spec_case_silent.

        (* simplify [getDir] *)
        unfold getDir in *; simpl in *.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac; try solve_msi_false.
            solve_rule_conds_ex.
            apply H0; rewrite H5; auto.
        + solve_sim_ext_mp.
          
      - (** [parentEvictRqImmM] *)
        disc_rule_conds_ex.
        spec_case_silent.

        (* simplify [getDir] *)
        unfold getDir in *; simpl in *.

        (* discharging [ImplStateInv] *)
        assert (msg_value rmsg = fst sost).
        { specialize (H16 ltac:(clear -H20; solve_msi)); dest.
          disc_DirMsgsCoh_by_FirstMP H16 H56.
          assert (msiM <= fst (snd cost2)).
          { apply H50; auto.
            { rewrite H20; auto. }
            { exists (c2pRq, rmsg); split.
              { apply FirstMP_InMP; assumption. }
              { unfold sigOf; simpl.
                rewrite H55, H9; reflexivity.
              }
            }
          }
          specialize (H16 ltac:(clear -H17; solve_msi)).
          congruence.
        }
        subst.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac; try solve_msi_false.
            apply DirMsgsCoh_other_msg_id_enqMP; [|solve_not_in].
            apply DirMsgsCoh_deqMP.
            assumption.
        + solve_sim_ext_mp.
    Qed.          
    
    Theorem MsiSv_ok:
      (steps step_m) # (steps step_m) |-- impl ⊑ spec.
    Proof.
      apply invSim_implies_refinement with (ginv:= ImplInvEx) (sim:= SimMSI).
      - apply simMsiSv_sim.
      - red; unfold ImplInvEx; intros.
        dest; split.
        + eapply implInv_invStep; eauto.
        + eapply implInvB_invStep; eauto.
      - apply simMsiSv_init.
      - split.
        + apply implInv_init.
        + apply implInvB_init.
    Qed.

  End Facts.
  
End Sim.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

