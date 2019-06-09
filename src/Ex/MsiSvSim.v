Require Import Bool List String Peano_dec Lia.
Require Import Common FMap HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Msi MsiSv SpecSv MsiSvTopo (* MsiSvInv *).

Set Implicit Arguments.

Import MonadNotations.
Import CaseNotations.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

(** TODO: move to [MsiSvInv.v] *)
Ltac solve_msi :=
  unfold msiM, msiS, msiI in *; lia.

Ltac solve_not_in :=
  intro; dest_in; discriminate.

Ltac solve_DisjList :=
  match goal with
  | [ |- DisjList ?ll ?rl] =>
    let e := fresh "e" in
    red; intro e;
    destruct (in_dec eq_nat_dec e ll); [right|auto];
    dest_in; solve_not_in
  end.

Section Sim.

  Local Definition spec := SpecSv.spec 1.
  Local Definition impl := MsiSv.impl.

  (** Simulation between states *)

  Definition ImplOStateMSI (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    msiS <= ost#[implStatusIdx] -> ost#[implValueIdx] = cv.

  Section DirCoh.
    Variables (cv: nat)
              (dir: MSI)
              (cost: OState ImplOStateIfc)
              (pc cpRq cpRs: IdxT)
              (msgs: MessagePool Msg).

    Definition DirMsgCoh (idm: Id Msg) :=
      match case (sigOf idm) on sig_dec default True with
      | (pc, (MRs, msiRsS)): (valOf idm).(msg_value) = VNat cv
      | (cpRs, (MRs, msiDownRsS)): (valOf idm).(msg_value) = VNat cv
      | (cpRq, (MRq, msiRqI)): (valOf idm).(msg_value) = VNat cv
      end.
    
    Definition DirMsgsCoh :=
      forall idm, InMPI msgs idm -> DirMsgCoh idm.

    Definition DirCoh :=
      msiS <= dir -> ImplOStateMSI cv cost /\ DirMsgsCoh.

  End DirCoh.

  Definition DirCohEx (dir: nat) (cost: OState ImplOStateIfc)
             (pc cpRq cpRs: IdxT) (msgs: MessagePool Msg) :=
    exists cv, DirCoh cv dir cost pc cpRq cpRs msgs.

  Section DirExcl.
    Variables (dir: MSI)
              (cost: OState ImplOStateIfc)
              (pc cpRq cpRs: IdxT)
              (msgs: MessagePool Msg).

    Definition DirMsgRsM :=
      exists idm,
        InMPI msgs idm /\ sigOf idm = (pc, (MRs, msiRsM)).

    Definition DirMsgDownRsS :=
      exists idm,
        InMPI msgs idm /\ sigOf idm = (cpRs, (MRs, msiDownRsS)).

    Definition DirExcl :=
      (dir = msiM -> DirMsgRsM -> cost#[implStatusIdx] = msiI) /\
      (DirMsgDownRsS -> dir = msiM).

  End DirExcl.

  Section DirInv.
    Variables (post cost1 cost2: OState ImplOStateIfc)
              (porq corq1 corq2: ORq Msg)
              (msgs: MessagePool Msg).

    Definition DirSound1: Prop :=
      !corq1@[upRq]; cost1#[implStatusIdx] <= post#[implDirIdx].(fst).

    Definition DirSound2: Prop :=
      !corq2@[upRq]; cost2#[implStatusIdx] <= post#[implDirIdx].(snd).

    Definition DirSoundS: Prop :=
      (post#[implDirIdx].(fst) = msiS \/ post#[implDirIdx].(snd) = msiS) ->
      post#[implStatusIdx] = msiS.

    Definition DirExcl1: Prop :=
      msiM <= post#[implDirIdx].(fst) ->
      post#[implStatusIdx] = msiI /\ post#[implDirIdx].(snd) = msiI.

    Definition DirExcl2: Prop :=
      msiM <= post#[implDirIdx].(snd) ->
      post#[implStatusIdx] = msiI /\ post#[implDirIdx].(fst) = msiI.

    (** TODO: check [DirSoundS], [DirExcl1], and [DirExcl2]
     * can be in simulation. *)
    Definition DirInv: Prop :=
      DirSound1 /\ DirSound2 /\
      DirSoundS /\ DirExcl1 /\ DirExcl2.

  End DirInv.

  Section DownLockInv.
    Variables (post: OState ImplOStateIfc)
              (porq: ORq Msg).

    Definition ParentDownLockBack: Prop :=
      rqid <+- porq@[downRq];
        (rqid.(rqi_minds_rss) = [c1pRs] -> rqid.(rqi_midx_rsb) = pc2) /\
        (rqid.(rqi_minds_rss) = [c2pRs] -> rqid.(rqi_midx_rsb) = pc1).

    Definition DownLockInv: Prop :=
      ParentDownLockBack.

  End DownLockInv.

  Definition ImplStateCoh (cv: nat) (st: MState ImplOStateIfc): Prop :=
    post <-- (bst_oss st)@[parentIdx];
      cost1 <-- (bst_oss st)@[child1Idx];
      cost2 <-- (bst_oss st)@[child2Idx];
      corq1 <-- (bst_orqs st)@[child1Idx];
      corq2 <-- (bst_orqs st)@[child2Idx];
      ImplOStateMSI cv post /\
      DirCoh cv post#[implDirIdx].(fst) cost1 pc1 c1pRq c1pRs (bst_msgs st) /\
      DirCoh cv post#[implDirIdx].(snd) cost2 pc2 c2pRq c2pRs (bst_msgs st).

  Definition ImplStateInv (st: MState ImplOStateIfc): Prop :=
    post <-- (bst_oss st)@[parentIdx];
      cost1 <-- (bst_oss st)@[child1Idx];
      cost2 <-- (bst_oss st)@[child2Idx];
      porq <-- (bst_orqs st)@[parentIdx];
      corq1 <-- (bst_orqs st)@[child1Idx];
      corq2 <-- (bst_orqs st)@[child2Idx];
      DirInv post cost1 cost2 corq1 corq2 /\
      DirExcl post#[implDirIdx].(fst) cost1 pc1 c1pRs (bst_msgs st) /\
      DirExcl post#[implDirIdx].(snd) cost2 pc2 c2pRs (bst_msgs st) /\
      DirCohEx post#[implDirIdx].(fst) cost1 pc1 c1pRq c1pRs (bst_msgs st) /\
      DirCohEx post#[implDirIdx].(snd) cost2 pc2 c2pRq c2pRs (bst_msgs st) /\
      DownLockInv porq.

  Definition SpecStateCoh (cv: nat) (st: MState SpecOStateIfc): Prop :=
    sost <-- (bst_oss st)@[specIdx];
      sorq <-- (bst_orqs st)@[specIdx];
      sost#[specValueIdx] = cv.

  Inductive SimState: MState ImplOStateIfc -> MState SpecOStateIfc -> Prop :=
  | SimStateIntro:
      forall cv ist sst,
        SpecStateCoh cv sst ->
        ImplStateCoh cv ist ->
        SimState ist sst.

  Definition SimExtMP (imsgs: MessagePool Msg) (iorqs: ORqs Msg)
             (smsgs: MessagePool Msg) :=
    corq1 <-- iorqs@[child1Idx];
      corq2 <-- iorqs@[child2Idx];
      (corq1@[upRq] >>= (fun rqiu1 => Some rqiu1.(rqi_msg)))
        ::> (findQ ec1 imsgs) = findQ (erq 0) smsgs /\
      (corq2@[upRq] >>= (fun rqiu2 => Some rqiu2.(rqi_msg)))
        ::> (findQ ec2 imsgs) = findQ (erq 1) smsgs /\
      findQ ce1 imsgs = findQ (ers 0) smsgs /\
      findQ ce2 imsgs = findQ (ers 1) smsgs.
  
  Definition SimMSI (ist: MState ImplOStateIfc) (sst: MState SpecOStateIfc): Prop :=
    SimState ist sst /\
    SimExtMP ist.(bst_msgs) ist.(bst_orqs) sst.(bst_msgs).

  Hint Unfold ImplOStateMSI DirCoh DirExcl
       DirSound1 DirSound2 DirSoundS DirExcl1 DirExcl2 DirInv
       ParentDownLockBack DownLockInv
       ImplStateCoh ImplStateInv: RuleConds.

  Section Facts.

    (* Lemma implNoCohMsgs_DirMsgsCoh_1: *)
    (*   forall cost1 cost2 msgs, *)
    (*     ImplNoCohMsgs cost1 cost2 msgs -> *)
    (*     forall cv, DirMsgsCoh cv pc1 c1pRq c1pRs msgs. *)
    (* Proof. *)
    (*   unfold ImplNoCohMsgs, DirMsgsCoh; intros. *)
    (*   specialize (H _ H0). *)
    (*   unfold caseDec in *. *)
    (*   repeat (destruct (sig_dec _ _); [exfalso; auto; fail|]). *)
    (*   destruct (sig_dec _ _). *)
    (*   find_if_inside. *)
    (*   repeat (find_if_inside; [exfalso; auto; fail|]). *)
    (*   find_if_inside; [intros; exfalso; rewrite H in H1; solve_msi|]. *)
    (*   find_if_inside; [intros; exfalso; rewrite H in H1; solve_msi|]. *)
    (*   auto. *)
    (* Qed. *)

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
      - destruct (in_dec eq_nat_dec ec1 (idsOf eins)).
        + apply in_map_iff in i.
          destruct i as [[midx msg] ?]; dest; simpl in *; subst.
          do 2 (erewrite findQ_In_NoDup_enqMsgs; eauto).
          rewrite ocons_app; congruence.
        + do 2 (rewrite findQ_not_In_enqMsgs by assumption).
          assumption.
      - destruct (in_dec eq_nat_dec ec2 (idsOf eins)).
        + apply in_map_iff in i.
          destruct i as [[midx msg] ?]; dest; simpl in *; subst.
          do 2 (erewrite findQ_In_NoDup_enqMsgs; eauto).
          rewrite ocons_app; congruence.
        + do 2 (rewrite findQ_not_In_enqMsgs by assumption).
          assumption.
      - destruct (in_dec eq_nat_dec ce1 (idsOf eins)).
        + apply in_map_iff in i.
          destruct i as [[midx msg] ?]; dest; simpl in *; subst.
          do 2 (erewrite findQ_In_NoDup_enqMsgs; eauto).
          congruence.
        + do 2 (rewrite findQ_not_In_enqMsgs by assumption).
          assumption.
      - destruct (in_dec eq_nat_dec ce2 (idsOf eins)).
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
      - destruct (in_dec eq_nat_dec ec1 (idsOf eouts)).
        + exfalso.
          destruct H; apply H in i.
          dest_in; discriminate.
        + do 2 (rewrite findQ_not_In_deqMsgs by assumption).
          assumption.
      - destruct (in_dec eq_nat_dec ec2 (idsOf eouts)).
        + exfalso.
          destruct H; apply H in i.
          dest_in; discriminate.
        + do 2 (rewrite findQ_not_In_deqMsgs by assumption).
          assumption.
      - destruct (in_dec eq_nat_dec ce1 (idsOf eouts)).
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
      - destruct (in_dec eq_nat_dec ce2 (idsOf eouts)).
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
        rqiu1.(rqi_msg) = msg ->
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
        rqiu2.(rqi_msg) = msg ->
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
      forall imsgs (orqs: ORqs Msg) smsgs porq1 norq1,
        orqs@[child1Idx] = Some porq1 ->
        porq1@[upRq] <> None -> norq1@[upRq] = None ->
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
      rewrite <-H0.
      unfold findQ; mred.
    Qed.

    Lemma SimExtMP_spec_deqMP_unlocked_2:
      forall imsgs (orqs: ORqs Msg) smsgs porq2 norq2,
        orqs@[child2Idx] = Some porq2 ->
        porq2@[upRq] <> None -> norq2@[upRq] = None ->
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
      rewrite <-H2.
      unfold findQ; mred.
    Qed.

    (* Definition cohMsgIds: list IdxT := *)
    (*   [msiRsS; msiDownRsS; msiRqI]. *)
    
    (* Lemma ImplMsgsCoh_other_msg_id_enqMP: *)
    (*   forall cv cost1 cost2 msgs, *)
    (*     ImplMsgsCoh cv cost1 cost2 msgs -> *)
    (*     forall midx msg, *)
    (*       ~ In (msg_id msg) cohMsgIds -> *)
    (*       ImplMsgsCoh cv cost1 cost2 (enqMP midx msg msgs). *)
    (* Proof. *)
    (* Admitted. *)

    (* Lemma ImplMsgsCoh_other_msg_id_enqMsgs: *)
    (*   forall cv cost1 cost2 msgs, *)
    (*     ImplMsgsCoh cv cost1 cost2 msgs -> *)
    (*     forall eins, *)
    (*       DisjList (map (fun idm => msg_id (valOf idm)) eins) cohMsgIds -> *)
    (*       ImplMsgsCoh cv cost1 cost2 (enqMsgs eins msgs). *)
    (* Proof. *)
    (*   intros. *)
    (*   generalize dependent msgs. *)
    (*   induction eins as [|ein eins]; simpl; intros; [assumption|]. *)
    (*   destruct ein as [midx msg]; simpl in *. *)
    (*   apply DisjList_cons in H0; dest. *)
    (*   eapply IHeins; eauto. *)
    (*   apply ImplMsgsCoh_other_msg_id_enqMP; auto. *)
    (* Qed. *)

    (* Definition cohMinds: list IdxT := *)
    (*   [pc1; pc2; c1pRs; c2pRs; c1pRq; c2pRq]. *)

    (* Lemma ImplMsgsCoh_other_midx_enqMP: *)
    (*   forall cv cost1 cost2 msgs, *)
    (*     ImplMsgsCoh cv cost1 cost2 msgs -> *)
    (*     forall midx msg, *)
    (*       ~ In midx cohMinds -> *)
    (*       ImplMsgsCoh cv cost1 cost2 (enqMP midx msg msgs). *)
    (* Proof. *)
    (* Admitted. *)

    (* Lemma ImplMsgsCoh_other_midx_enqMsgs: *)
    (*   forall cv cost1 cost2 msgs, *)
    (*     ImplMsgsCoh cv cost1 cost2 msgs -> *)
    (*     forall eins, *)
    (*       DisjList (idsOf eins) cohMinds -> *)
    (*       ImplMsgsCoh cv cost1 cost2 (enqMsgs eins msgs). *)
    (* Proof. *)
    (*   intros. *)
    (*   generalize dependent msgs. *)
    (*   induction eins as [|ein eins]; simpl; intros; [assumption|]. *)
    (*   destruct ein as [midx msg]; simpl in *. *)
    (*   apply DisjList_cons in H0; dest. *)
    (*   eapply IHeins; eauto. *)
    (*   apply ImplMsgsCoh_other_midx_enqMP; auto. *)
    (* Qed. *)

    (* Lemma ImplMsgsCoh_deqMP: *)
    (*   forall cv cost1 cost2 msgs, *)
    (*     ImplMsgsCoh cv cost1 cost2 msgs -> *)
    (*     forall midx, *)
    (*       ImplMsgsCoh cv cost1 cost2 (deqMP midx msgs). *)
    (* Proof. *)
    (*   unfold ImplMsgsCoh; intros. *)
    (*   apply InMP_deqMP in H0; auto. *)
    (* Qed. *)

    (* Lemma ImplMsgsCoh_deqMsgs: *)
    (*   forall cv cost1 cost2 msgs, *)
    (*     ImplMsgsCoh cv cost1 cost2 msgs -> *)
    (*     forall minds, *)
    (*       ImplMsgsCoh cv cost1 cost2 (deqMsgs minds msgs). *)
    (* Proof. *)
    (*   unfold ImplMsgsCoh; intros. *)
    (*   apply InMP_deqMsgs in H0; auto. *)
    (* Qed. *)

    (* Lemma SimState_impl_other_msg_id_enqMsgs: *)
    (*   forall ioss iorqs imsgs sst, *)
    (*     SimState {| bst_oss := ioss; bst_orqs := iorqs; bst_msgs := imsgs |} sst -> *)
    (*     forall nmsgs, *)
    (*       DisjList (map (fun idm => msg_id (valOf idm)) nmsgs) cohMsgIds -> *)
    (*       SimState {| bst_oss := ioss; bst_orqs := iorqs; *)
    (*                   bst_msgs := enqMsgs nmsgs imsgs |} sst. *)
    (* Proof. *)
    (*   intros. *)
    (*   inv H. *)
    (*   apply SimStateIntro with (cv:= cv); [assumption|]. *)
    (*   clear H1. *)
    (*   red in H2; red; simpl in *. *)
    (*   disc_rule_conds_ex. *)
    (*   repeat split; try assumption. *)
    (*   eapply ImplMsgsCoh_other_msg_id_enqMsgs; eauto. *)
    (* Qed. *)

    (* Lemma SimState_impl_other_midx_enqMsgs: *)
    (*   forall ioss iorqs imsgs sst, *)
    (*     SimState {| bst_oss := ioss; bst_orqs := iorqs; bst_msgs := imsgs |} sst -> *)
    (*     forall nmsgs, *)
    (*       DisjList (idsOf nmsgs) cohMinds -> *)
    (*       SimState {| bst_oss := ioss; bst_orqs := iorqs; *)
    (*                   bst_msgs := enqMsgs nmsgs imsgs |} sst. *)
    (* Proof. *)
    (*   intros. *)
    (*   inv H. *)
    (*   apply SimStateIntro with (cv:= cv); [assumption|]. *)
    (*   clear H1. *)
    (*   red in H2; red; simpl in *. *)
    (*   disc_rule_conds_ex. *)
    (*   repeat split; try assumption. *)
    (*   eapply ImplMsgsCoh_other_midx_enqMsgs; eauto. *)
    (* Qed. *)

    Lemma SimState_spec_enqMsgs:
      forall ist soss sorqs smsgs,
        SimState ist {| bst_oss := soss; bst_orqs := sorqs; bst_msgs := smsgs |} ->
        forall nmsgs,
          SimState ist {| bst_oss := soss; bst_orqs := sorqs;
                          bst_msgs := enqMsgs nmsgs smsgs |}.
    Proof.
      intros.
      inv H.
      econstructor; eauto.
    Qed.

    (* Lemma SimState_impl_deqMsgs: *)
    (*   forall ioss iorqs imsgs sst, *)
    (*     SimState {| bst_oss := ioss; bst_orqs := iorqs; bst_msgs := imsgs |} sst -> *)
    (*     forall minds, *)
    (*       SimState {| bst_oss := ioss; bst_orqs := iorqs; *)
    (*                   bst_msgs := deqMsgs minds imsgs |} sst. *)
    (* Proof. *)
    (*   intros. *)
    (*   inv H. *)
    (*   apply SimStateIntro with (cv:= cv); [assumption|]. *)
    (*   clear H0. *)
    (*   red in H1; red; simpl in *. *)
    (*   disc_rule_conds_ex. *)
    (*   repeat split; try assumption. *)
    (*   clear -H0. *)
    (*   red in H0; red; intros. *)
    (*   apply InMP_deqMsgs in H; auto. *)
    (* Qed. *)

    Lemma SimState_spec_deqMsgs:
      forall ist soss sorqs smsgs,
        SimState ist {| bst_oss := soss; bst_orqs := sorqs; bst_msgs := smsgs |} ->
        forall minds,
          SimState ist {| bst_oss := soss; bst_orqs := sorqs;
                          bst_msgs := deqMsgs minds smsgs |}.
    Proof.
      intros.
      inv H.
      econstructor; eauto.
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
        |solve_DisjList]
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
        |solve_DisjList]
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
        |solve_DisjList]
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
         | [ |- SimExtMP (deqMP _ _) _ (deqMP _ _) ] =>
           eapply SimExtMP_outs_deqMP_child_1; eauto; fail
         | [ |- SimExtMP (enqMP _ _ _) _ _ ] =>
           apply SimExtMP_impl_enqMP_indep; [solve_not_in; fail|]
         | [ |- SimExtMP (deqMP _ _) _ _ ] =>
           eapply SimExtMP_spec_deqMP_locked_1; eauto; [mred|reflexivity]; fail
         | [ |- SimExtMP (deqMP _ _) _ _ ] =>
           apply SimExtMP_impl_deqMP_indep; [solve_not_in; fail|]
         | [ |- SimExtMP _ _ (deqMP _ _) ] =>
           eapply SimExtMP_spec_deqMP_unlocked_1; eauto; [congruence|mred]; fail
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

    Ltac pull_uplock_facts oidx :=
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
          (* apply SimState_impl_other_midx_enqMsgs; [assumption|]. *)
          (* destruct H1. *)
          (* eapply DisjList_SubList; [eassumption|]. *)
          (* solve_DisjList. *)
          admit.
        * apply SimExtMP_enqMsgs; auto.
          apply H1.
    Admitted.

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
          (* apply SimState_impl_deqMsgs. *)
          (* assumption. *)
          admit.
        * apply SimExtMP_ext_outs_deqMsgs; auto.
    Admitted.

    Lemma simMsiSv_sim:
      InvSim step_m step_m ImplStateInv SimMSI impl spec.
    Proof.
      red; intros.
      inv H2;
        [apply simMsiSv_sim_silent; assumption
        |apply simMsiSv_sim_ext_in; assumption
        |apply simMsiSv_sim_ext_out; assumption
        |].

      pose proof (footprints_ok
                    msiSv_impl_ORqsInit
                    msiSv_impl_GoodRqRsSys H) as Hftinv.

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

      - (** [childGetRqImm] *)
        disc_rule_conds_ex.
        spec_case_get 0 ec1.

        assert (pos#[implValueIdx] = fst sost).
        { solve_rule_conds_ex.
          apply H15; [|assumption].
          clear -H1 H18.
          solve_msi.
        }
        simpl in H4; rewrite H4 in *.
        
        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { admit. }
            { solve_rule_conds_ex. }
            { admit. }
        + solve_sim_ext_mp.

      - (** [childGetRqS] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { admit. }
            { solve_rule_conds_ex. }
            { admit. }
        + solve_sim_ext_mp.

      - (** [childGetRsS] *)
        disc_rule_conds_ex.
        spec_case_get 0 ec1;
          [unfold FirstMPI, FirstMP, firstMP;
           simpl; change ec1 with (erq 0);
           rewrite <-H2; reflexivity|].

        pull_uplock_facts child1Idx.

        assert (n = fst sost)
          by (disc_DirMsgsCoh_by_FirstMP H12 H41; congruence).
        subst.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { solve_rule_conds_ex. }
            { admit. }
            { solve_rule_conds_ex. }
            { admit. }
        + solve_sim_ext_mp.

      - (** [childDownRqS] *)
        disc_rule_conds_ex.
        spec_case_silent.
        
        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { admit. }
            { solve_rule_conds_ex. }
            { admit. }
        + solve_sim_ext_mp.

      - (** [childSetRqImm] *)
        disc_rule_conds_ex.
        spec_case_set 0 ec1.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= n).
          * rewrite Hmsg.
            solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { clear -H9; intros; solve_msi. }
            { admit. }
            { clear -H12 H29; intros; solve_msi. }
            { admit. }
        + solve_sim_ext_mp.

      - (** [childSetRqM] *)
        disc_rule_conds_ex.
        spec_case_silent.
        
        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { admit. }
            { solve_rule_conds_ex. }
            { admit. }
        + solve_sim_ext_mp.
          
      - (** [childSetRsM] *)
        disc_rule_conds_ex.
        spec_case_set 0 ec1;
          [unfold FirstMPI, FirstMP, firstMP;
           simpl; change ec1 with (erq 0);
           rewrite <-H2; reflexivity|].

        pull_uplock_facts child1Idx.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= n).
          * rewrite Hmsg.
            solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { clear -H28; intros; solve_msi. }
            { admit. }
            { clear -H4 H39; intros; solve_msi. }
            { admit. }
        + solve_sim_ext_mp.

      - (** [childDownRqI] *)
        disc_rule_conds_ex.
        spec_case_silent.
        
        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { admit. }
            { solve_rule_conds_ex. }
            { admit. }
        + solve_sim_ext_mp.

      - (** [childEvictRqI] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { admit. }
            { solve_rule_conds_ex. }
            { admit. }
        + solve_sim_ext_mp.

      - (** [childEvictRsI] *)
        disc_rule_conds_ex.
        spec_case_evict 0 ec1;
          [unfold FirstMPI, FirstMP, firstMP;
           simpl; change ec1 with (erq 0);
           rewrite <-H2; reflexivity|].

        pull_uplock_facts child1Idx.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { solve_rule_conds_ex. }
            { clear; intros; solve_msi. }
            { admit. }
            { solve_rule_conds_ex. }
            { admit. }
        + solve_sim_ext_mp.

      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.
      - admit.

      - (** [parentGetRqImm] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { solve_rule_conds_ex. }
            { destruct H20 as [cv ?].
              disc_rule_conds_ex.
              red in H20.
              specialize (H20 (pc1, _) (InMP_or_enqMP
                                          (deqMP c1pRq msgs)
                                          (or_introl (conj eq_refl eq_refl)))).
              red in H20; simpl in H20.
              congruence.
            }
            { admit. }
            { solve_rule_conds_ex. }
            { admit. }
        + solve_sim_ext_mp.

      - (** [parentGetDownRqS] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { admit. }
            { solve_rule_conds_ex. }
            { admit. }
        + solve_sim_ext_mp.

      - (** [parentSetRqImm] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { clear; intros; solve_msi. }
            { intros; exfalso.
              rewrite H12 in H5; [clear -H5; solve_msi|].
              eexists (_, _); split.
              { apply InMP_or_enqMP; simpl; auto. }
              { reflexivity. }
            }
            { admit. }
            { solve_rule_conds_ex. }
            { admit. }
        + solve_sim_ext_mp.

      - (** [parentSetDownRqI] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { admit. }
            { solve_rule_conds_ex. }
            { admit. }
        + solve_sim_ext_mp.

      - (** [parentGetDownRsS] *)
        disc_rule_conds_ex.
        spec_case_silent.

        inv H43.
        specialize (H9 eq_refl).
        rewrite H34 in H16
          by (eexists; split;
              [apply FirstMP_InMP; eassumption
              |unfold sigOf; simpl; congruence]).
        specialize (H16 ltac:(solve_msi)); dest.
        disc_DirMsgsCoh_by_FirstMP H12 H17.
        rewrite H12 in Hmsg; inv Hmsg.
        rewrite H9 in *.

        move H20 at bottom.
        destruct H20 as [cv ?].
        specialize (H16 ltac:(solve_msi)); dest.
        specialize (H20 (pc1, _) (InMP_or_enqMP
                                    (deqMP c2pRs msgs)
                                    (or_introl (conj eq_refl eq_refl)))).
        red in H20; simpl in H20.
        inv H20.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { assumption. }
            { admit. }
            { assumption. }
            { admit. }
        + solve_sim_ext_mp.

      - (** [parentSetDownRsI] *)
        disc_rule_conds_ex.
        spec_case_silent.

        inv H43.
        specialize (H9 eq_refl).
        rewrite H9 in *.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { clear; intros; solve_msi. }
            { intros; exfalso.
              rewrite H18 in H33; [clear -H33; solve_msi|].
              eexists (_, _); split.
              { apply InMP_or_enqMP; simpl; auto. }
              { reflexivity. }
            }
            { admit. }
            { clear -H5; intros; solve_msi. }
            { admit. }
        + admit.

      - (** [parentEvictRqImmI] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { solve_rule_conds_ex. }
            { solve_rule_conds_ex. }
            { admit. }
            { solve_rule_conds_ex. }
            { admit. }
        + solve_sim_ext_mp.

      - (** [parentEvictRqImmS] *)
        disc_rule_conds_ex.
        spec_case_silent.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { solve_rule_conds_ex. }
            { clear -H4; solve_msi. }
            { admit. }
            { solve_rule_conds_ex. }
            { admit. }
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
            repeat split.
            { solve_rule_conds_ex.
              apply H0.
              rewrite H39; auto.
            }
            { clear -H4; solve_msi. }
            { clear -H4; solve_msi. }
            { solve_rule_conds_ex. }
            { admit. }
        + solve_sim_ext_mp.
          
      - (** [parentEvictRqImmM] *)
        disc_rule_conds_ex.
        spec_case_silent.

        (* simplify [getDir] *)
        unfold getDir in *; simpl in *.

        (* discharging [ImplStateInv] *)
        assert (n = fst sost).
        { specialize (H15 ltac:(solve_msi)); dest.
          disc_DirMsgsCoh_by_FirstMP H5 H43.
          congruence.
        }
        subst.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            repeat split.
            { clear -H4; solve_msi. }
            { clear -H4; solve_msi. }
            { solve_rule_conds_ex. }
            { admit. }
        + solve_sim_ext_mp.
          
    Admitted.
    
    Theorem MsiSv_ok:
      (steps step_m) # (steps step_m) |-- impl ⊑ spec.
    Proof.
      apply invSim_implies_refinement with (ginv:= ImplStateInv) (sim:= SimMSI).
      - apply simMsiSv_sim.
      - admit.
      - apply simMsiSv_init.
      - admit.
    Admitted.

  End Facts.
  
End Sim.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

