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

Ltac solve_DisjList :=
  match goal with
  | [ |- DisjList ?ll ?rl] =>
    let e := fresh "e" in
    red; intro e;
    destruct (in_dec eq_nat_dec e ll); [right|auto];
    dest_in; intro; dest_in; discriminate
  end.

Section Sim.

  Local Definition spec := SpecSv.spec 1.
  Local Definition impl := MsiSv.impl.

  (** Simulation between states *)

  Definition ImplOStateMSI (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] >= msiS -> ost#[implValueIdx] = cv.

  Section ImplCoh.
    Variables (cv: nat)
              (post cost1 cost2: OState ImplOStateIfc)
              (porq corq1 corq2: ORq Msg)
              (msgs: MessagePool Msg).

    Definition ParentCoh: Prop :=
      ImplOStateMSI cv post.
    Definition ImplChildCoh1: Prop :=
      !corq1@[upRq]; ImplOStateMSI cv cost1.
    Definition ImplChildCoh2: Prop :=
      !corq2@[upRq]; ImplOStateMSI cv cost2.

    Definition ImplOStateCoh: Prop :=
      ParentCoh /\ ImplChildCoh1 /\ ImplChildCoh2.

    Definition ImplMsgsCoh :=
      forall idm,
        InMPI msgs idm ->
        match case (sigOf idm) on sig_dec default True with
        | (pc1, (MRs, msiRsS)): (valOf idm).(msg_value) = VNat cv
        | (pc2, (MRs, msiRsS)): (valOf idm).(msg_value) = VNat cv
        | (c1pRs, (MRs, msiDownRsS)): (valOf idm).(msg_value) = VNat cv
        | (c2pRs, (MRs, msiDownRsS)): (valOf idm).(msg_value) = VNat cv
        | (c1pRq, (MRq, msiRqI)):
            (cost1#[implStatusIdx] >= msiS -> (valOf idm).(msg_value) = VNat cv)
        | (c2pRq, (MRq, msiRqI)):
            (cost2#[implStatusIdx] >= msiS -> (valOf idm).(msg_value) = VNat cv)
        end.
             
    Definition ImplCoh :=
      ImplOStateCoh /\ ImplMsgsCoh.

  End ImplCoh.

  Definition ChildInvalid (cost: OState ImplOStateIfc) (corq: ORq Msg) :=
    cost#[implStatusIdx] = msiI \/ corq@[upRq] <> None.

  Definition ChildExcl (cost: OState ImplOStateIfc) (corq: ORq Msg) :=
    cost#[implStatusIdx] = msiM /\ corq@[upRq] = None.

  Section ImplExcl.
    Variables (post cost1 cost2: OState ImplOStateIfc)
              (porq corq1 corq2: ORq Msg)
              (msgs: MessagePool Msg).

    Definition ImplNoCohMsgs: Prop :=
      forall idm,
        InMPI msgs idm ->
        match case (sigOf idm) on sig_dec default True with
        | (pc1, (MRs, msiRsS)): False
        | (pc2, (MRs, msiRsS)): False
        | (c1pRs, (MRs, msiDownRsS)): False
        | (c2pRs, (MRs, msiDownRsS)): False
        | (c1pRq, (MRq, msiRqI)): cost1#[implStatusIdx] = msiI
        | (c2pRq, (MRq, msiRqI)): cost2#[implStatusIdx] = msiI
        end.

    Definition ImplExcl: Prop :=
      (ChildExcl cost1 corq1 ->
       post#[implStatusIdx] = msiI /\ ChildInvalid cost2 corq2 /\ ImplNoCohMsgs) /\
      (ChildExcl cost2 corq2 ->
       post#[implStatusIdx] = msiI /\ ChildInvalid cost1 corq1 /\ ImplNoCohMsgs).

  End ImplExcl.

  Definition ImplStateCoh (cv: nat) (st: MState ImplOStateIfc): Prop :=
    post <-- (bst_oss st)@[parentIdx];
      cost1 <-- (bst_oss st)@[child1Idx];
      cost2 <-- (bst_oss st)@[child2Idx];
      corq1 <-- (bst_orqs st)@[child1Idx];
      corq2 <-- (bst_orqs st)@[child2Idx];
      ImplCoh cv post cost1 cost2 corq1 corq2 (bst_msgs st).

  Definition ImplStateExcl (st: MState ImplOStateIfc): Prop :=
    post <-- (bst_oss st)@[parentIdx];
      cost1 <-- (bst_oss st)@[child1Idx];
      cost2 <-- (bst_oss st)@[child2Idx];
      corq1 <-- (bst_orqs st)@[child1Idx];
      corq2 <-- (bst_orqs st)@[child2Idx];
      ImplExcl post cost1 cost2 corq1 corq2 (bst_msgs st).

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

  Hint Unfold ImplOStateMSI ParentCoh
       ImplChildCoh1 ImplChildCoh2 ImplOStateCoh ImplCoh
       ChildInvalid ChildExcl ImplExcl: RuleConds.

  Section Facts.

    Lemma implNoCohMsgs_ImplMsgsCoh:
      forall cost1 cost2 msgs,
        ImplNoCohMsgs cost1 cost2 msgs ->
        forall cv, ImplMsgsCoh cv cost1 cost2 msgs.
    Proof.
      unfold ImplNoCohMsgs, ImplMsgsCoh; intros.
      specialize (H _ H0).
      unfold caseDec in *.
      repeat (find_if_inside; [exfalso; auto; fail|]).
      find_if_inside; [intros; exfalso; rewrite H in H1; solve_msi|].
      find_if_inside; [intros; exfalso; rewrite H in H1; solve_msi|].
      auto.
    Qed.

    Lemma simMsiSv_init:
      SimMSI (initsOf impl) (initsOf spec).
    Proof.
      split.
      - apply SimStateIntro with (cv:= 0).
        + reflexivity.
        + repeat split.
          vm_compute; intros; exfalso; auto.
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

    Lemma ImplMsgsCoh_other_enqMP:
      forall cv cost1 cost2 msgs,
        ImplMsgsCoh cv cost1 cost2 msgs ->
        forall midx msg,
          ~ In midx [pc1; pc2; c1pRs; c2pRs; c1pRq; c2pRq] ->
          ImplMsgsCoh cv cost1 cost2 (enqMP midx msg msgs).
    Proof.
    Admitted.

    Lemma ImplMsgsCoh_other_enqMsgs:
      forall cv cost1 cost2 msgs,
        ImplMsgsCoh cv cost1 cost2 msgs ->
        forall eins minds,
          SubList (idsOf eins) minds ->
          DisjList minds [pc1; pc2; c1pRs; c2pRs; c1pRq; c2pRq] ->
          ImplMsgsCoh cv cost1 cost2 (enqMsgs eins msgs).
    Proof.
      intros.
      generalize dependent msgs.
      induction eins as [|ein eins]; simpl; intros; [assumption|].
      simpl in H0; apply SubList_cons_inv in H0; dest.
      destruct ein as [midx msg]; simpl in *.
      eapply IHeins; eauto.
      apply ImplMsgsCoh_other_enqMP; auto.
      eapply DisjList_In_2; eauto.
    Qed.

    Lemma ImplMsgsCoh_deqMP:
      forall cv cost1 cost2 msgs,
        ImplMsgsCoh cv cost1 cost2 msgs ->
        forall midx,
          ImplMsgsCoh cv cost1 cost2 (deqMP midx msgs).
    Proof.
      unfold ImplMsgsCoh; intros.
      apply InMP_deqMP in H0; auto.
    Qed.

    Lemma ImplMsgsCoh_other_deqMsgs:
      forall cv cost1 cost2 msgs,
        ImplMsgsCoh cv cost1 cost2 msgs ->
        forall minds,
          ImplMsgsCoh cv cost1 cost2 (deqMsgs minds msgs).
    Proof.
      unfold ImplMsgsCoh; intros.
      apply InMP_deqMsgs in H0; auto.
    Qed.

    Lemma SimState_impl_ext_enqMsgs:
      forall ioss iorqs imsgs sst,
        SimState {| bst_oss := ioss; bst_orqs := iorqs; bst_msgs := imsgs |} sst ->
        forall nmsgs,
          SubList (idsOf nmsgs) (sys_merqs impl) ->
          SimState {| bst_oss := ioss; bst_orqs := iorqs;
                      bst_msgs := enqMsgs nmsgs imsgs |} sst.
    Proof.
      intros.
      inv H.
      apply SimStateIntro with (cv:= cv); [assumption|].
      clear H1.
      red in H2; red; simpl in *.
      disc_rule_conds_ex.
      repeat split; try assumption.
      eapply ImplMsgsCoh_other_enqMsgs; eauto.
      solve_DisjList.
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
      repeat split; try assumption.
      clear -H0.
      red in H0; red; intros.
      apply InMP_deqMsgs in H; auto.
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
    
    Ltac spec_case_silent cidx ecmidx :=
      idtac; exists (RlblEmpty _); eexists;
      repeat ssplit;
      [reflexivity
      |econstructor
      |].

    Lemma simMsiSv_sim:
      InvSim step_m step_m ImplStateExcl SimMSI impl spec.
    Proof.
      red; intros.
      inv H2.

      - simpl; exists (RlblEmpty _); eexists.
        repeat ssplit; eauto.
        constructor.

      - destruct sst1 as [soss1 sorqs1 smsgs1]; simpl in *.
        destruct H0; simpl in *.
        exists (RlblIns eins); eexists.
        repeat ssplit.
        + reflexivity.
        + eapply SmIns; eauto.
        + split.
          * apply SimState_spec_enqMsgs.
            apply SimState_impl_ext_enqMsgs; [assumption|].
            apply H5.
          * apply SimExtMP_enqMsgs; auto.
            apply H5.

      - destruct sst1 as [soss1 sorqs1 smsgs1]; simpl in *.
        destruct H0; simpl in *.
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

      - pose proof (footprints_ok
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

        + (** [childGetRqImm] *)
          disc_rule_conds_ex.
          spec_case_get 0 ec1.

          red; simpl; split.
          * eapply SimStateIntro with (cv:= fst sost).
            { solve_rule_conds_ex. }
            { red; simpl.
              disc_rule_conds_ex.
              split.
              { solve_rule_conds_ex. }
              { apply ImplMsgsCoh_other_enqMP;
                  [|intro; dest_in; discriminate].
                apply ImplMsgsCoh_deqMP.
                assumption.
              }
            }
          * replace (orqs +[child1Idx <- norq]) with orqs by meq.
            specialize (H5 eq_refl H19); rewrite H5.
            apply SimExtMP_enqMP.
            eapply SimExtMP_outs_deqMP_child_1; eauto.

        + (** [childGetRqS] *)
          disc_rule_conds_ex.
          spec_case_silent 0 ec1.
                    
          red; simpl; split.
          * eapply SimStateIntro with (cv:= fst sost).
            { solve_rule_conds_ex. }
            { red; simpl.
              disc_rule_conds_ex.
              split.
              { solve_rule_conds_ex. }
              { admit. }
            }
          * admit.

        + (** [childGetRsS] *)
          disc_rule_conds_ex.
          spec_case_get 0 ec1;
            [unfold FirstMPI, FirstMP, firstMP;
             simpl; change ec1 with (erq 0);
             rewrite <-H2; reflexivity|].
          
          good_footprint_get child1Idx.
          destruct H15 as [rqFrom [rqTo [rsFrom [rsbTo ?]]]]; dest.
          disc_rule_conds_ex.
          pose proof (parentIdxOf_child_indsOf _ _ H23).
          dest_in; try discriminate; simpl in *.
          inv H26; inv H27.

          assert (n = fst sost).
          { specialize (H4 _ (FirstMP_InMP H20)).
            unfold sigOf, valOf, snd in H4.
            rewrite H21, H22 in H4; simpl in H4.
            congruence.
          }
          subst.

          red; simpl; split.
          * eapply SimStateIntro with (cv:= fst sost).
            { solve_rule_conds_ex. }
            { red; simpl.
              disc_rule_conds_ex.
              split.
              { solve_rule_conds_ex. }
              { admit. }
            }
          * apply SimExtMP_enqMP.
            apply SimExtMP_impl_deqMP_indep; [intro Hx; dest_in; discriminate|].
            eapply SimExtMP_spec_deqMP_unlocked_1; eauto.
            { congruence. }
            { mred. }

        + (** [childDownRqS] *)
          disc_rule_conds_ex.
          spec_case_silent 0 ec1.
                    
          red; simpl; split.
          * eapply SimStateIntro with (cv:= fst sost).
            { solve_rule_conds_ex. }
            { red; simpl.
              disc_rule_conds_ex.
              split.
              { solve_rule_conds_ex.
                apply H5; auto.
              }
              { admit. }
            }
          * admit.

        + (** [childSetRqImm] *)
          disc_rule_conds_ex.
          spec_case_set 0 ec1.

          (* discharging [ImplStateExcl] *)
          red in H3; simpl in H3.
          disc_rule_conds_ex.
          specialize (H3 (conj eq_refl eq_refl)); dest.

          red; simpl; split.
          * eapply SimStateIntro with (cv:= n).
            { rewrite Hmsg.
              solve_rule_conds_ex.
            }
            { red; simpl.
              disc_rule_conds_ex.
              split.
              { solve_rule_conds_ex.
                { solve_msi. }
                { destruct H12; [solve_msi|exfalso; auto]. }
              }
              { apply implNoCohMsgs_ImplMsgsCoh; assumption. }
            }
          * replace (orqs +[child1Idx <- norq]) with orqs by meq.
            apply SimExtMP_enqMP.
            eapply SimExtMP_outs_deqMP_child_1; eauto.
          
        + (** [childSetRqM] *)
          disc_rule_conds_ex.
          spec_case_silent 0 ec1.
                    
          red; simpl; split.
          * eapply SimStateIntro with (cv:= fst sost).
            { solve_rule_conds_ex. }
            { red; simpl.
              disc_rule_conds_ex.
              split.
              { solve_rule_conds_ex. }
              { admit. }
            }
          * admit.
          
        + (** [childSetRsM] *)
          disc_rule_conds_ex.
          spec_case_set 0 ec1;
            [unfold FirstMPI, FirstMP, firstMP;
             simpl; change ec1 with (erq 0);
             rewrite <-H2; reflexivity|].

          (* discharging [ImplStateExcl] *)
          red in H3; simpl in H3.
          disc_rule_conds_ex.
          specialize (H3 (conj eq_refl eq_refl)); dest.

          red; simpl; split.
          * eapply SimStateIntro with (cv:= n).
            { rewrite Hmsg.
              solve_rule_conds_ex.
            }
            { red; simpl.
              disc_rule_conds_ex.
              split.
              { solve_rule_conds_ex.
                { solve_msi. }
                { destruct H18; [solve_msi|exfalso; auto]. }
              }
              { apply implNoCohMsgs_ImplMsgsCoh; assumption. }
            }
          * admit.

        + (** [childDownRqI] *)
          disc_rule_conds_ex.
          spec_case_silent 0 ec1.
                    
          red; simpl; split.
          * eapply SimStateIntro with (cv:= fst sost).
            { solve_rule_conds_ex. }
            { red; simpl.
              disc_rule_conds_ex.
              split.
              { solve_rule_conds_ex.
                apply H5; auto.
              }
              { admit. }
            }
          * admit.

        + (** [childEvictRqI] *)
          disc_rule_conds_ex.
          spec_case_silent 0 ec1.

          red; simpl; split.
          * eapply SimStateIntro with (cv:= fst sost).
            { solve_rule_conds_ex. }
            { red; simpl.
              disc_rule_conds_ex.
              split.
              { solve_rule_conds_ex. }
              { admit. }
            }
          * admit.

        + (** [childEvictRsI] *)
          admit.
          
    Admitted.
    
    Theorem MsiSv_ok:
      (steps step_m) # (steps step_m) |-- impl ⊑ spec.
    Proof.
      apply invSim_implies_refinement with (ginv:= ImplStateExcl) (sim:= SimMSI).
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

