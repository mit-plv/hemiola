Require Import Bool List String Peano_dec Lia.
Require Import Common FMap HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Msi MsiSv SpecSv MsiSvTopo MsiSvInv.

Set Implicit Arguments.

Import MonadNotations.
Import CaseNotations.

Open Scope list.
Open Scope hvec.
Open Scope fmap.


Lemma ocons_app:
  forall {A} (oa: option A) l1 l2,
    ocons oa (l1 ++ l2) = ocons oa l1 ++ l2.
Proof.
  destruct oa as [a|]; simpl; intros; reflexivity.
Qed.

Section Sim.

  Local Definition spec := SpecSv.spec 1.
  Local Definition impl := MsiSv.impl.

  (** Simulation between states *)

  Definition SpecState (v: nat) (oss: OStates SpecOStateIfc): Prop :=
    sost <-- oss@[specIdx]; sost#[specValueIdx] = v.

  Definition SimState (ioss: OStates ImplOStateIfc) (iorqs: ORqs Msg)
             (soss: OStates SpecOStateIfc): Prop :=
    post <-- ioss@[parentIdx];
      cost1 <-- ioss@[child1Idx];
      cost2 <-- ioss@[child2Idx];
      porq <-- iorqs@[parentIdx];
      corq1 <-- iorqs@[child1Idx];
      corq2 <-- iorqs@[child2Idx];
      (exists cv,
          ImplStateCoh post cost1 cost2 porq corq1 corq2 cv /\
          SpecState cv soss).

  Definition SimMP (imsgs: MessagePool Msg) (iorqs: ORqs Msg)
             (smsgs: MessagePool Msg) :=
    corq1 <-- iorqs@[child1Idx];
      corq2 <-- iorqs@[child2Idx];
      (* (findQ ec1 imsgs) *)
      (*   ++ (oll [(corq1@[upRq] >>= (fun rqiu1 => Some rqiu1.(rqi_msg)))]) = *)
      (* findQ (erq 0) smsgs /\ *)
      (* (findQ ec2 imsgs) *)
      (*   ++ (oll [(corq2@[upRq] >>= (fun rqiu2 => Some rqiu2.(rqi_msg)))]) = *)
      (* findQ (erq 1) smsgs /\ *)
      (corq1@[upRq] >>= (fun rqiu1 => Some rqiu1.(rqi_msg)))
        ::> (findQ ec1 imsgs) = findQ (erq 0) smsgs /\
      (corq2@[upRq] >>= (fun rqiu2 => Some rqiu2.(rqi_msg)))
        ::> (findQ ec2 imsgs) = findQ (erq 1) smsgs /\
      findQ ce1 imsgs = findQ (ers 0) smsgs /\
      findQ ce2 imsgs = findQ (ers 1) smsgs.
  
  Definition SimMSI (ist: MState ImplOStateIfc) (sst: MState SpecOStateIfc): Prop :=
    SimState ist.(bst_oss) ist.(bst_orqs) sst.(bst_oss) /\
    SimMP ist.(bst_msgs) ist.(bst_orqs) sst.(bst_msgs).

  Section Facts.

    Lemma SimMsiSv_init:
      SimMSI (initsOf impl) (initsOf spec).
    Proof.
      vm_compute.
      split.
      - exists 0; split.
        + firstorder.
        + reflexivity.
      - repeat split.
    Qed.

    Lemma SimMP_enqMsgs:
      forall eins,
        NoDup (idsOf eins) ->
        forall imsgs orqs smsgs,
          SimMP imsgs orqs smsgs ->
          SimMP (enqMsgs eins imsgs) orqs (enqMsgs eins smsgs).
    Proof.
      unfold SimMP; intros.
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

    Lemma SimMP_ext_outs_deqMsgs:
      forall eouts,
        ValidMsgsExtOut impl eouts ->
        forall imsgs orqs smsgs,
          Forall (FirstMPI imsgs) eouts ->
          SimMP imsgs orqs smsgs ->
          SimMP (deqMsgs (idsOf eouts) imsgs) orqs (deqMsgs (idsOf eouts) smsgs).
    Proof.
      unfold SimMP; intros.
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

    Lemma SimMP_ext_outs_FirstMPI:
      forall eouts,
        ValidMsgsExtOut impl eouts ->
        forall imsgs orqs smsgs,
          SimMP imsgs orqs smsgs ->
          Forall (FirstMPI imsgs) eouts ->
          Forall (FirstMPI smsgs) eouts.
    Proof.
      unfold SimMP; intros.
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

    Lemma SimMsiSv_sim:
      InvSim step_m step_m ImplStateInv SimMSI impl spec.
    Proof.
      red; intros.
      inv H2; [simpl; eauto|..].

      - destruct sst1 as [soss1 sorqs1 smsgs1]; simpl in *.
        destruct H0; simpl in *.
        do 2 eexists.
        repeat ssplit.
        + eapply SmIns; eauto.
        + reflexivity.
        + split; [assumption|].
          apply SimMP_enqMsgs; auto.
          apply H4.

      - destruct sst1 as [soss1 sorqs1 smsgs1]; simpl in *.
        destruct H0; simpl in *.
        do 2 eexists.
        repeat ssplit; simpl.
        + eapply SmOuts with (msgs0:= smsgs1); eauto.
          eapply SimMP_ext_outs_FirstMPI; eauto.
        + reflexivity.
        + split; [assumption|].
          simpl.
          apply SimMP_ext_outs_deqMsgs; auto.

      - 
        
    Admitted.
    
    Theorem MsiSv_ok:
      (steps step_m) # (steps step_m) |-- impl ⊑ spec.
    Proof.
      apply invSim_implies_refinement
        with (ginv:= ImplStateInv)
             (sim:= SimMSI).
      - apply SimMsiSv_sim.
      - apply ImplStateInv_invStep.
      - apply SimMsiSv_init.
      - apply ImplStateInv_init.
    Qed.

  End Facts.
  
End Sim.

