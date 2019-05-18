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

Section Sim.

  Local Definition spec := SpecSv.spec 1.
  Local Definition impl := MsiSv.impl.

  (** Simulation between states *)

  Definition SpecState (v: nat) (oss: OStates SpecOStateIfc)
             (orqs: ORqs Msg): Prop :=
    sost <-- oss@[specIdx];
      sorq <-- orqs@[specIdx];
      sost#[specValueIdx] = v.

  Definition SimState (ioss: OStates ImplOStateIfc) (iorqs: ORqs Msg)
             (soss: OStates SpecOStateIfc) (sorqs: ORqs Msg): Prop :=
    cost1 <-- ioss@[child1Idx];
      cost2 <-- ioss@[child2Idx];
      corq1 <-- iorqs@[child1Idx];
      corq2 <-- iorqs@[child2Idx];
      (exists cv,
          ImplChildCoh1 cost1 corq1 cv /\
          ImplChildCoh2 cost2 corq2 cv /\
          SpecState cv soss sorqs).

  Definition SimMP (imsgs: MessagePool Msg) (iorqs: ORqs Msg)
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
    SimState ist.(bst_oss) ist.(bst_orqs) sst.(bst_oss) sst.(bst_orqs) /\
    SimMP ist.(bst_msgs) ist.(bst_orqs) sst.(bst_msgs).

  Section Facts.

    Lemma simMsiSv_init:
      SimMSI (initsOf impl) (initsOf spec).
    Proof.
      vm_compute.
      split.
      - exists 0; repeat split.
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

    Lemma SimMP_enqMP:
      forall midx msg imsgs orqs smsgs,
        SimMP imsgs orqs smsgs ->
        SimMP (enqMP midx msg imsgs) orqs (enqMP midx msg smsgs).
    Proof.
      intros.
      eapply SimMP_enqMsgs with (eins:= [(midx, msg)]) in H; auto.
      repeat constructor; intro; dest_in.
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

    Lemma SimMP_outs_deqMP_child_1:
      forall msg imsgs (orqs: ORqs Msg) smsgs corq1,
        orqs@[child1Idx] = Some corq1 ->
        corq1@[upRq] = None ->
        FirstMPI imsgs (ec1, msg) ->
        SimMP imsgs orqs smsgs ->
        SimMP (deqMP ec1 imsgs) orqs (deqMP ec1 smsgs).
    Proof.
      unfold SimMP; intros.
      disc_rule_conds_ex.
      repeat split;
        try (do 2 (rewrite findQ_not_In_deqMP by discriminate);
             assumption).

      (* TODO: extract to a lemma? *)
      clear -H2.
      unfold deqMP.
      rewrite H2.
      change ec1 with (erq 0) in *.
      destruct (findQ (erq 0) smsgs) eqn:Hq.
      - congruence.
      - unfold findQ; mred.
    Qed.
      
    Lemma SimMP_outs_deqMP_child_2:
      forall msg imsgs (orqs: ORqs Msg) smsgs corq2,
        orqs@[child2Idx] = Some corq2 ->
        corq2@[upRq] = None ->
        FirstMPI imsgs (ec2, msg) ->
        SimMP imsgs orqs smsgs ->
        SimMP (deqMP ec2 imsgs) orqs (deqMP ec2 smsgs).
    Proof.
      unfold SimMP; intros.
      disc_rule_conds_ex.
      repeat split;
        try (do 2 (rewrite findQ_not_In_deqMP by discriminate);
             assumption).

      (* TODO: extract to a lemma? *)
      clear -H3.
      unfold deqMP.
      rewrite H3.
      change ec2 with (erq 1) in *.
      destruct (findQ (erq 1) smsgs) eqn:Hq.
      - congruence.
      - unfold findQ; mred.
    Qed.

    Lemma SimMP_impl_deqMP_indep:
      forall midx imsgs (orqs: ORqs Msg) smsgs,
        ~ In midx [ce1; ce2; ec1; ec2] ->
        SimMP imsgs orqs smsgs ->
        SimMP (deqMP midx imsgs) orqs smsgs.
    Proof.
      unfold SimMP; intros.
      disc_rule_conds_ex.
      repeat split;
        try (rewrite findQ_not_In_deqMP
              by (intro; subst; clear -H; firstorder);
             assumption).
    Qed.

    Lemma SimMP_spec_deqMP_unlocked_1:
      forall imsgs (orqs: ORqs Msg) smsgs porq1 norq1,
        orqs@[child1Idx] = Some porq1 ->
        porq1@[upRq] <> None -> norq1@[upRq] = None ->
        SimMP imsgs orqs smsgs ->
        SimMP imsgs (orqs +[child1Idx <- norq1]) (deqMP ec1 smsgs).
    Proof.
      unfold SimMP; intros.
      disc_rule_conds_ex.
      repeat split;
        try (rewrite findQ_not_In_deqMP by discriminate;
             assumption).
      unfold deqMP.
      change ec1 with (erq 0).
      rewrite <-H0.
      unfold findQ; mred.
    Qed.

    Lemma SimMP_spec_deqMP_unlocked_2:
      forall imsgs (orqs: ORqs Msg) smsgs porq2 norq2,
        orqs@[child2Idx] = Some porq2 ->
        porq2@[upRq] <> None -> norq2@[upRq] = None ->
        SimMP imsgs orqs smsgs ->
        SimMP imsgs (orqs +[child2Idx <- norq2]) (deqMP ec2 smsgs).
    Proof.
      unfold SimMP; intros.
      disc_rule_conds_ex.
      repeat split;
        try (rewrite findQ_not_In_deqMP by discriminate;
             assumption).
      unfold deqMP.
      change ec2 with (erq 1).
      rewrite <-H2.
      unfold findQ; mred.
    Qed.
    
    Lemma simMsiSv_sim:
      InvSim step_m step_m ImplInv SimMSI impl spec.
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
        + split; [assumption|].
          apply SimMP_enqMsgs; auto.
          apply H5.

      - destruct sst1 as [soss1 sorqs1 smsgs1]; simpl in *.
        destruct H0; simpl in *.
        exists (RlblOuts eouts); eexists.
        repeat ssplit.
        + reflexivity.
        + eapply SmOuts with (msgs0:= smsgs1); eauto.
          eapply SimMP_ext_outs_FirstMPI; eauto.
        + split; [assumption|].
          apply SimMP_ext_outs_deqMsgs; auto.

      - pose proof (footprints_ok
                      msiSv_impl_ORqsInit
                      msiSv_impl_GoodRqRsSys H) as Hftinv.

        destruct sst1 as [soss1 sorqs1 smsgs1].
        destruct H0; simpl in H0, H2; simpl.
        red in H0; disc_rule_conds_const.
        destruct H0 as [cv ?]; dest.
        red in H15; disc_rule_conds_const.
        destruct H4 as [|[|[|]]];
          try (exfalso; auto; fail); subst; dest_in.

        + (** [childGetRqImm] *)
          disc_rule_conds_ex.
          eexists (RlblInt 0 (rule_idx (specGetRq 0)) _ _); eexists.
          repeat ssplit.
          * reflexivity.
          * eapply SmInt with (obj:= specObj 1);
              try reflexivity; try eassumption.
            { left; reflexivity. }
            { simpl; tauto. }
            { instantiate (1:= [(ec1, rmsg)]).
              repeat constructor.
              red in H2; disc_rule_conds_ex.
              eapply findQ_eq_FirstMPI; eauto.
            }
            { split.
              { simpl; apply SubList_cons; [|apply SubList_nil].
                simpl; tauto.
              }
              { repeat constructor; intro Hx; dest_in. }
            }
            { solve_rule_conds_ex. }
            { clear; solve_rule_conds_ex.
              { simpl; tauto. }
              { repeat constructor; intro Hx; dest_in. }
            }
            { disc_rule_conds_ex. }
          * red; simpl; split.
            { solve_rule_conds_ex. }
            { replace (orqs +[child1Idx <- norq]) with orqs by meq.
              specialize (H0 eq_refl H15); rewrite H0.
              apply SimMP_enqMP.
              eapply SimMP_outs_deqMP_child_1; eauto.
            }

        + (** [childGetRqS] *)
          admit.

        + (** [childGetRsS] *)
          disc_rule_conds_ex.
          eexists (RlblInt 0 (rule_idx (specGetRq 0)) _ _); eexists.
          repeat ssplit.
          * reflexivity.
          * eapply SmInt with (obj:= specObj 1);
              try reflexivity; try eassumption.
            { left; reflexivity. }
            { simpl; tauto. }
            { instantiate (1:= [(ec1, rqi_msg rqi)]).
              repeat constructor.
              red in H2.
              disc_rule_conds_ex.
              clear -H2.
              unfold FirstMPI, FirstMP, firstMP; simpl.
              unfold ec1.
              rewrite <-H2.
              reflexivity.
            }
            { split.
              { simpl; apply SubList_cons; [|apply SubList_nil].
                simpl; tauto.
              }
              { repeat constructor; intro Hx; dest_in. }
            }
            { solve_rule_conds_ex. }
            { clear; solve_rule_conds_ex.
              { simpl; tauto. }
              { repeat constructor; intro Hx; dest_in. }
            }
            { disc_rule_conds_ex.
              (** TODO: develop [solve_sublist] and [solve_disjlist]. *)
              red; intro e.
              destruct (in_dec eq_nat_dec e [ec1]); [right|auto].
              dest_in; intro; dest_in; discriminate.
            }
          * red; simpl; split.
            { (** TODO: need to know the response message value is
               *  coherent as well. This is part of predicate messages but
               *  [ImplStateInv] does not contain it.
               *)
              admit.
            }
            { replace (fst ost1) with n by admit.
              good_footprint_get child1Idx.
              red in H9.
              destruct H9 as [rqFrom [rqTo [rsFrom [rsbTo ?]]]]; dest.
              disc_rule_conds_ex.
              pose proof (parentIdxOf_child_indsOf _ _ H19).
              dest_in; try discriminate; simpl in *.
              inv H22; inv H23.
              apply SimMP_enqMP.
              apply SimMP_impl_deqMP_indep; [intro Hx; dest_in; discriminate|].
              eapply SimMP_spec_deqMP_unlocked_1; eauto.
              { congruence. }
              { mred. }
            }

        + (** [childDownRqS] *)

    Admitted.
    
    Theorem MsiSv_ok:
      (steps step_m) # (steps step_m) |-- impl ⊑ spec.
    Proof.
      apply invSim_implies_refinement with (ginv:= ImplInv) (sim:= SimMSI).
      - apply simMsiSv_sim.
      - apply implInv_invStep.
      - apply simMsiSv_init.
      - apply implInv_init.
    Qed.

  End Facts.
  
End Sim.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

