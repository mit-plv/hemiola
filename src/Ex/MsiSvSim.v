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

Ltac solve_msi_false :=
  exfalso; try congruence;
  match goal with
  | [H: msiS <= msiI |- _] => clear -H; solve_msi
  | [H: msiM <= msiI |- _] => clear -H; solve_msi
  | [H: msiM <= msiS |- _] => clear -H; solve_msi
  | [H1: ?t = msiI, H2: msiS <= ?t |- _] =>
    rewrite H1 in H2; clear -H2; solve_msi
  | [H1: ?t = msiI, H2: msiM <= ?t |- _] =>
    rewrite H1 in H2; clear -H2; solve_msi
  | [H1: ?t = msiS, H2: msiM <= ?t |- _] =>
    rewrite H1 in H2; clear -H2; solve_msi
  end.

Ltac solve_not_in :=
  intro; dest_in; discriminate.

Ltac solve_SubList :=
  red; intros; dest_in; simpl; tauto.

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

    Definition MsgExistsRqI :=
      exists idm, InMPI msgs idm /\ sigOf idm = (c1pRq, (MRq, msiRqI)).

    Definition DirExcl :=
      msiM <= dir -> MsgExistsRqI -> msiM <= cost#[implStatusIdx].

    Definition ExclInv :=
      ChildExcl /\ DirExcl.

  End InvExcl.

  Section InvInvalid.
    Variables (dir: MSI)
              (cost: OState ImplOStateIfc)
              (pc cpRq cpRs: IdxT)
              (msgs: MessagePool Msg).

    Definition MsgExistsRsI :=
      exists idm, InMPI msgs idm /\ sigOf idm = (pc, (MRs, msiRsI)).

    Definition ChildInvalid :=
      cost#[implStatusIdx] = msiI \/ MsgExistsRsI.
    
    Definition InvalidInv :=
      dir = msiI ->
      ChildInvalid /\ InvalidMsgs cost pc cpRq cpRs msgs.

  End InvInvalid.

  Section InvDir.
    Variables (post cost1 cost2: OState ImplOStateIfc)
              (porq corq1 corq2: ORq Msg)
              (msgs: MessagePool Msg).

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

    (* Why soundness of the shared status:
     * the parent is upgraded to M when all children values are evicted.
     * In this case the parent does not update the value, but maintain the
     * value since the protocol is write-through. But in order to check
     * correctness we need to know the parent status is S when all children
     * values are evicted.
     *)
    Definition DirSoundS: Prop :=
      (post#[implDirIdx].(fst) = msiS \/ post#[implDirIdx].(snd) = msiS) ->
      post#[implStatusIdx] = msiS.

    (* Why exclusiveness of the directory:
     * It's simple. We need to know [P.st = C2.st = I] when [C1.st = M] and
     * [C1] is lock-free. By the soundness of the directory, we can get
     * [P.dir.C1 = M]. Then by this exclusiveness, we can get
     * [P.st = P.dir.C2 = I].
     *)
    Definition DirExcl1: Prop :=
      msiM <= post#[implDirIdx].(fst) ->
      post#[implStatusIdx] = msiI /\ post#[implDirIdx].(snd) = msiI.

    Definition DirExcl2: Prop :=
      msiM <= post#[implDirIdx].(snd) ->
      post#[implStatusIdx] = msiI /\ post#[implDirIdx].(fst) = msiI.

    Definition DirCorrectM: Prop :=
      msiM <= post#[implStatusIdx] ->
      post#[implDirIdx].(fst) = msiI /\ post#[implDirIdx].(snd) = msiI.
    
    Definition DirCorrectS: Prop :=
      post#[implStatusIdx] = msiS ->
      (post#[implDirIdx].(fst) <= msiS /\ post#[implDirIdx].(snd) <= msiS).
    
    Definition DirInv: Prop :=
      DirSound1 /\ DirSound2 /\ DirSoundS /\
      DirExcl1 /\ DirExcl2 /\
      DirCorrectM /\ DirCorrectS.

  End InvDir.

  Section DownLockInv.
    Variables (post: OState ImplOStateIfc)
              (porq: ORq Msg).

    Definition ParentDownRsS1 (rqid: RqInfo Msg): Prop :=
      rqid.(rqi_msg).(msg_id) = msiDownRqS ->
      msiM <= post#[implDirIdx].(snd).
      
    Definition ParentDownRsS2 (rqid: RqInfo Msg): Prop :=
      rqid.(rqi_msg).(msg_id) = msiDownRqS ->
      msiM <= post#[implDirIdx].(fst).

    Definition ParentDownRsI1 (rqid: RqInfo Msg): Prop :=
      rqid.(rqi_msg).(msg_id) = msiDownRqI ->
      msiS <= post#[implDirIdx].(snd).

    Definition ParentDownRsI2 (rqid: RqInfo Msg): Prop :=
      rqid.(rqi_msg).(msg_id) = msiDownRqI ->
      msiS <= post#[implDirIdx].(fst).

    Definition ParentDownLockBack: Prop :=
      rqid <+- porq@[downRq];
        (rqid.(rqi_minds_rss) = [c1pRs] ->
         rqid.(rqi_midx_rsb) = pc2 /\ ParentDownRsS2 rqid /\ ParentDownRsS2 rqid) /\
        (rqid.(rqi_minds_rss) = [c2pRs] ->
         rqid.(rqi_midx_rsb) = pc1 /\ ParentDownRsS1 rqid /\ ParentDownRsI1 rqid).

    Definition DownLockInv: Prop :=
      ParentDownLockBack.

  End DownLockInv.

  Section DirCoh.
    Variables (cv: nat)
              (dir: MSI)
              (cost: OState ImplOStateIfc)
              (corq: ORq Msg)
              (pc cpRq cpRs: IdxT)
              (msgs: MessagePool Msg).

    Definition DirMsgCoh (idm: Id Msg) :=
      match case (sigOf idm) on sig_dec default True with
      | (pc, (MRs, msiRsS)): (valOf idm).(msg_value) = VNat cv
      | (cpRs, (MRs, msiDownRsS)): (valOf idm).(msg_value) = VNat cv
      | (cpRq, (MRq, msiRqI)):
          (msiS <= cost#[implStatusIdx] -> (valOf idm).(msg_value) = VNat cv)
      end.
    
    Definition DirMsgsCoh :=
      forall idm, InMPI msgs idm -> DirMsgCoh idm.

    Definition DirCoh :=
      msiS <= dir -> ImplOStateMSI cv cost /\ DirMsgsCoh.

  End DirCoh.

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
      ExclInv post#[implDirIdx].(fst) cost1 corq1 pc1 c1pRq c1pRs (bst_msgs st) /\
      ExclInv post#[implDirIdx].(snd) cost2 corq2 pc2 c2pRq c2pRs (bst_msgs st) /\
      InvalidInv post#[implDirIdx].(fst) cost1 pc1 c1pRq c1pRs (bst_msgs st) /\
      InvalidInv post#[implDirIdx].(snd) cost2 pc2 c2pRq c2pRs (bst_msgs st) /\
      DownLockInv post porq.

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

  Hint Unfold ImplOStateMSI ChildExcl DirExcl ExclInv InvalidInv
       DirSound1 DirSound2 DirSoundS DirExcl1 DirExcl2
       DirCorrectM DirCorrectS DirInv
       ParentDownRsS1 ParentDownRsS2 ParentDownRsI1 ParentDownRsI2
       ParentDownLockBack DownLockInv
       DirCoh
       ImplStateCoh ImplStateInv: RuleConds.

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
      forall cv (cost1 cost2: OState ImplOStateIfc) pc cpRq cpRs msgs,
        DirMsgsCoh cv cost1 pc cpRq cpRs msgs ->
        cost2#[implStatusIdx] <= cost1#[implStatusIdx] ->
        DirMsgsCoh cv cost2 pc cpRq cpRs msgs.
    Proof.
      unfold DirMsgsCoh, DirMsgCoh; intros.
      specialize (H _ H1).
      unfold caseDec in *.
      repeat (destruct (sig_dec _ _); [auto; fail|]).
      destruct (sig_dec _ _).
      - intros; apply H; lia.
      - auto.
    Qed.

    Lemma DirMsgsCoh_no_RqI:
      forall cv (cost1 cost2: OState ImplOStateIfc) pc cpRq cpRs msgs,
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
      intros.
      inv H.
      econstructor; eauto.
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
          solve_DisjList.
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

    Lemma simMsiSv_sim:
      InvSim step_m step_m ImplStateInv SimMSI impl spec.
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

      - (** [childGetRqImm] *)
        disc_rule_conds_ex.
        spec_case_get 0 ec1.

        assert (pos#[implValueIdx] = fst sost).
        { solve_rule_conds_ex.
          apply H15; [|auto].
          clear -H1 H18; solve_msi.
        }
        simpl in H4; rewrite H4 in *.
        
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

        pull_uplock_minds child1Idx.
        clear Hnulinv.
        pull_uplock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
        disc_rule_conds_const.

        assert (n = fst sost)
          by (disc_DirMsgsCoh_by_FirstMP H12 H45; congruence).
        subst.

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
              destruct idm as [midx msg]; inv H52.
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

        rewrite H19 in H1.
        disc_rule_conds_ex.
              
        red; simpl; split.
        + eapply SimStateIntro with (cv:= n).
          * rewrite Hmsg.
            solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac; try solve_msi_false.
            apply invalidMsgs_DirMsgsCoh.
            apply H20; auto.
            clear -H19; solve_msi.
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

        clear Hnulinv; pull_uplock_minds child1Idx.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= n).
          * rewrite Hmsg.
            solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { solve_msi_false. }
            { apply invalidMsgs_DirMsgsCoh.
              rewrite <-H51 in H19.
              apply H19; auto.
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

        pull_uplock_minds child1Idx.

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
            destruct (Compare_dec.le_gt_dec msiM (fst (snd post))).
            { disc_rule_conds_ex.
              intuition idtac.
              { destruct H33.
                { exfalso; simpl in *; solve_msi_false. }
                { destruct H33 as [[midx msg] [? ?]]; inv H52.
                  clear Hpulinv.
                  pull_uplock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
                  disc_rule_conds_const.
                  exfalso.
                  exfalso_uplock_rs_two parentIdx pc1 msg.
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
            { assert (fst (snd post) = msiS) by (clear -g H18; solve_msi).
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
                  by (clear -H5 n; solve_msi).
                disc_rule_conds_ex.
                intuition idtac.
                { destruct H33.
                  { exfalso; simpl in *; solve_msi_false. }
                  { destruct H33 as [[midx msg] [? ?]]; inv H52.
                    clear Hpulinv.
                    pull_uplock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
                    disc_rule_conds_const.
                    exfalso.
                    exfalso_uplock_rs_two parentIdx pc1 msg.
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
              { destruct H5.
                { exfalso; simpl in *; solve_msi_false. }
                { destruct H5 as [[midx msg] [? ?]]; inv H51.
                  clear Hpulinv.
                  pull_uplock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
                  disc_rule_conds_const.
                  exfalso.
                  exfalso_uplock_rs_two parentIdx pc1 msg.
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

        inv H50.
        unfold setDir in *; simpl in *.

        (* Discharge the downlock invariant *)
        specialize (H35 eq_refl); dest.
        disc_rule_conds_ex.

        specialize (H16 ltac:(clear -H35; solve_msi)); dest.
        pose proof H50.
        disc_DirMsgsCoh_by_FirstMP H51 H44.
        rewrite Hmsg in H51; inv H51.

        red; simpl; split.
        + eapply SimStateIntro with (cv:= fst sost).
          * solve_rule_conds_ex.
          * red; simpl.
            disc_rule_conds_ex.
            intuition idtac.
            { destruct H33.
              { exfalso; simpl in *; solve_msi_false. }
              { destruct H33 as [[midx msg] [? ?]]; inv H55.
                clear Hpulinv.
                pull_uplock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
                disc_rule_conds_const.
                exfalso.
                exfalso_uplock_rs_two parentIdx pc1 msg.
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

        inv H50.
        unfold setDir in *; simpl in *.

        specialize (H46 eq_refl).
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
              { destruct H33.
                { exfalso; simpl in *; solve_msi_false. }
                { destruct H33 as [[midx msg] [? ?]]; inv H55.
                  clear Hpulinv.
                  pull_uplock_inv (child child1Idx ec1 ce1 c1pRq c1pRs pc1) impl.
                  disc_rule_conds_const.
                  exfalso.
                  exfalso_uplock_rs_two parentIdx pc1 msg.
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
            apply H0; rewrite H41; auto.
        + solve_sim_ext_mp.
          
      - (** [parentEvictRqImmM] *)
        disc_rule_conds_ex.
        spec_case_silent.

        (* simplify [getDir] *)
        unfold getDir in *; simpl in *.

        (* discharging [ImplStateInv] *)
        assert (n = fst sost).
        { specialize (H15 ltac:(clear -H19; solve_msi)); dest.
          disc_DirMsgsCoh_by_FirstMP H12 H47.
          assert (msiM <= fst (snd cost1)).
          { apply H39.
            { rewrite H19; auto. }
            { exists (c1pRq, rmsg); split.
              { apply FirstMP_InMP; assumption. }
              { unfold sigOf; simpl.
                rewrite H46, H6; reflexivity.
              }
            }
          }
          specialize (H12 ltac:(clear -H15; solve_msi)).
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

