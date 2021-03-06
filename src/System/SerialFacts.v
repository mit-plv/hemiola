Require Import Bool List String PeanoNat.
Require Import Common IndexSupport FMap.
Require Import Syntax Semantics SemFacts StepM Serial Invariant.

Require Import Lia.
Require Import Program.Equality.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Section MsgParam.
  Context `{dv: DecValue}.

  Lemma atomic_emptyILabel_not_in:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      ~ In RlblEmpty hst.
  Proof.
    induction 1; simpl; intros.
    - intro Hx; destruct Hx; [discriminate|auto].
    - intro Hx; destruct Hx; subst; [discriminate|auto].
  Qed.

  Lemma atomic_iLblIn_not_in:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      forall msg, ~ In (RlblIns [msg]) hst.
  Proof.
    induction 1; simpl; intros; [auto|];
      try (intro Hx; destruct Hx;
           [discriminate|firstorder]).
  Qed.

  Fixpoint insOfA (hst: History) :=
    match hst with
    | nil => nil
    | lbl :: hst' =>
      match lbl with
      | RlblInt _ _ ins _ => insOfA hst' ++ ins
      | _ => nil
      end
    end.

  Fixpoint outsOfA (hst: History) :=
    match hst with
    | nil => nil
    | lbl :: hst' =>
      match lbl with
      | RlblInt _ _ _ outs => outsOfA hst' ++ outs
      | _ => nil
      end
    end.

  Lemma atomic_lastOIdxOf:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      exists loidx,
        lastOIdxOf hst = Some loidx.
  Proof.
    induction 1; simpl; intros; eauto.
  Qed.

  Lemma atomic_ins:
    forall (hst: History) inits ins outs eouts,
      Atomic inits ins hst outs eouts ->
      ins = insOfA hst.
  Proof.
    induction 1; simpl; intros; subst; reflexivity.
  Qed.

  Lemma atomic_outs:
    forall (hst: History) inits ins outs eouts,
      Atomic inits ins hst outs eouts ->
      outs = outsOfA hst.
  Proof.
    induction 1; simpl; intros; subst; reflexivity.
  Qed.

  Lemma atomic_unique:
    forall (hst: History) inits1 ins1 outs1 eouts1,
      Atomic inits1 ins1 hst outs1 eouts1 ->
      forall inits2 ins2 outs2 eouts2,
        Atomic inits2 ins2 hst outs2 eouts2 ->
        inits1 = inits2 /\ ins1 = ins2 /\
        outs1 = outs2 /\ eouts1 = eouts2.
  Proof.
    induction 1; simpl; intros; subst.
    - inv H; [auto|inv H5].
    - inv H5; [inv H|].
      specialize (IHAtomic _ _ _ _ H8).
      dest; subst; auto.
  Qed.

  Lemma atomic_messages_spec_ValidDeqs:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      forall `{oifc: OStateIfc} (sys: System) st1 st2,
        steps step_m sys st1 hst st2 ->
        st_msgs st2 = deqMsgs (idsOf ins) (enqMsgs outs (st_msgs st1)) /\
        ValidDeqs (enqMsgs outs (st_msgs st1)) (idsOf ins).
  Proof.
    induction 1; simpl; intros; subst.
    - inv H; inv H3; inv H5; simpl; split.
      + apply enqMsgs_deqMsgs_comm; auto.
      + apply ValidDeqs_enqMsgs.
        destruct H10.
        apply FirstMPI_Forall_NoDup_ValidDeqs; auto.

    - inv H5.
      specialize (IHAtomic _ _ _ _ H6); dest.
      inv H8; simpl in *; subst.
      repeat rewrite idsOf_app, deqMsgs_app, enqMsgs_app.
      split.
      + rewrite enqMsgs_deqMsgs_comm with (minds1:= idsOf rins) by assumption.
        rewrite enqMsgs_deqMsgs_ValidDeqs_comm
          with (minds:= idsOf ins) (nmsgs:= routs) by assumption.
        reflexivity.
      + apply ValidDeqs_app.
        * apply ValidDeqs_enqMsgs; auto.
        * rewrite <-enqMsgs_deqMsgs_ValidDeqs_comm
            with (minds:= idsOf ins) (nmsgs:= routs) by assumption.
          destruct H16.
          apply ValidDeqs_enqMsgs; auto.
          apply FirstMPI_Forall_NoDup_ValidDeqs; auto.
  Qed.

  Corollary atomic_messages_spec:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      forall `{oifc: OStateIfc} (sys: System) st1 st2,
        steps step_m sys st1 hst st2 ->
        st_msgs st2 = deqMsgs (idsOf ins) (enqMsgs outs (st_msgs st1)).
  Proof.
    intros; eapply atomic_messages_spec_ValidDeqs; eauto.
  Qed.

  Lemma atomic_messages_inits_valid:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      forall `{oifc: OStateIfc} (sys: System) st1 st2,
        steps step_m sys st1 hst st2 ->
        ValidMsgsIn sys inits.
  Proof.
    induction 1; simpl; intros; subst.
    - inv_steps; inv_step; assumption.
    - inv_steps; eauto.
  Qed.

  Lemma atomic_messages_ins_outs:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      EquivList (inits ++ outs) (ins ++ eouts).
  Proof.
    induction 1; simpl; intros; subst;
      [apply EquivList_refl|].

    destruct IHAtomic; split.
    - repeat rewrite app_assoc.
      apply SubList_app_6; [|apply SubList_refl].
      eapply SubList_trans; [eassumption|].
      rewrite <-app_assoc.
      apply SubList_app_6; [apply SubList_refl|].
      apply removeL_SubList_3.
    - repeat rewrite app_assoc.
      apply SubList_app_6; [|apply SubList_refl].
      eapply SubList_trans; [|eassumption].
      rewrite <-app_assoc.
      apply SubList_app_6; [apply SubList_refl|].
      apply SubList_app_3; [assumption|].
      apply removeL_SubList_2.
  Qed.

  Lemma atomic_behavior_nil:
    forall (hst: History) inits ins outs eouts,
      Atomic inits ins hst outs eouts ->
      behaviorOf hst = nil.
  Proof.
    induction 1; simpl; intros; auto.
  Qed.

  Lemma atomic_singleton:
    forall oidx ridx ins outs,
      Atomic ins ins [RlblInt oidx ridx ins outs] outs outs.
  Proof.
    intros; constructor.
  Qed.

  Lemma extAtomic_unique:
    forall `{oifc: OStateIfc} (sys: System) inits1 hst eouts1,
      ExtAtomic sys inits1 hst eouts1 ->
      forall inits2 eouts2,
        ExtAtomic sys inits2 hst eouts2 ->
        inits1 = inits2 /\ eouts1 = eouts2.
  Proof.
    intros.
    inv H; inv H0.
    pose proof (atomic_unique H2 H3); dest; subst; auto.
  Qed.

  Lemma extAtomic_preserved:
    forall `{oifc: OStateIfc} (impl1: System) inits hst eouts,
      ExtAtomic impl1 inits hst eouts ->
      forall (impl2: System),
        sys_merqs impl1 = sys_merqs impl2 ->
        ExtAtomic impl2 inits hst eouts.
  Proof.
    intros.
    inv H.
    econstructor; eauto.
    rewrite <-H0; assumption.
  Qed.

  Lemma atomic_split_each:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      Forall AtomicEx (lift_each hst).
  Proof.
    induction 1; simpl; intros; [repeat econstructor|].
    repeat econstructor.
    assumption.
  Qed.

  Lemma atomicEx_split_each:
    forall hst,
      AtomicEx hst ->
      Forall AtomicEx (lift_each hst).
  Proof.
    unfold AtomicEx; intros; dest.
    eapply atomic_split_each; eauto.
  Qed.

  Definition InternalLbl (lbl: RLabel) :=
    match lbl with
    | RlblInt _ _ _ _ => True
    | _ => False
    end.

  Definition InsLbl (lbl: RLabel) :=
    match lbl with
    | RlblIns _ => True
    | _ => False
    end.

  Definition OutsLbl (lbl: RLabel) :=
    match lbl with
    | RlblOuts _ => True
    | _ => False
    end.

  Definition NonInsLbl (lbl: RLabel) :=
    match lbl with
    | RlblIns _ => False
    | _ => True
    end.

  Definition NonOutsLbl (lbl: RLabel) :=
    match lbl with
    | RlblOuts _ => False
    | _ => True
    end.

  Definition HistoryP (P: RLabel -> Prop) (hst: History) :=
    Forall (fun lbl => P lbl) hst.

  Definition InternalHistory := HistoryP InternalLbl.
  Definition InsHistory := HistoryP InsLbl.
  Definition OutsHistory := HistoryP OutsLbl.
  Definition NonInsHistory := HistoryP NonInsLbl.
  Definition NonOutsHistory := HistoryP NonOutsLbl.

  Lemma atomic_internal_history:
    forall inits ins hst outs eouts,
      Atomic inits ins hst outs eouts ->
      InternalHistory hst.
  Proof.
    induction 1; simpl; intros.
    - repeat constructor.
    - repeat constructor; auto.
  Qed.

  Lemma atomicEx_internal_history:
    forall hst,
      AtomicEx hst ->
      InternalHistory hst.
  Proof.
    unfold AtomicEx; intros; dest.
    eapply atomic_internal_history; eauto.
  Qed.

  Lemma sequential_nil:
    forall `{oifc: OStateIfc} (sys: System), Sequential sys nil nil.
  Proof.
    intros; hnf; intros.
    split.
    - constructor.
    - reflexivity.
  Qed.

  Lemma sequential_cons:
    forall `{oifc: OStateIfc} (sys: System) ll trss,
      Sequential sys ll trss ->
      forall trs,
        Transactional sys trs ->
        Sequential sys (trs ++ ll) (trs :: trss).
  Proof.
    intros.
    inv H.
    constructor; auto.
  Qed.

  Lemma sequential_silent:
    forall `{oifc: OStateIfc} (sys: System) ll trss,
      Sequential sys ll trss ->
      Sequential sys (RlblEmpty :: ll) ([RlblEmpty] :: trss).
  Proof.
    intros.
    hnf; hnf in H; dest.
    split.
    - constructor; [|eassumption].
      constructor.
    - subst; reflexivity.
  Qed.

  Lemma sequential_msg_ins:
    forall `{oifc: OStateIfc} (sys: System) ll trss eins,
      Sequential sys ll trss ->
      Sequential sys (RlblIns eins :: ll) ([RlblIns eins] :: trss).
  Proof.
    intros.
    hnf; hnf in H; dest.
    split.
    - constructor; [|eassumption].
      eapply TrsIns; reflexivity.
    - subst; reflexivity.
  Qed.

  Lemma sequential_msg_outs:
    forall `{oifc: OStateIfc} (sys: System) ll trss eouts,
      Sequential sys ll trss ->
      Sequential sys (RlblOuts eouts :: ll) ([RlblOuts eouts] :: trss).
  Proof.
    intros.
    hnf; hnf in H; dest.
    split.
    - constructor; [|eassumption].
      eapply TrsOuts; reflexivity.
    - subst; reflexivity.
  Qed.

  Lemma sequential_insHistory:
    forall `{oifc: OStateIfc} (sys: System) ins,
      InsHistory ins ->
      Sequential sys ins (lift_each ins).
  Proof.
    induction ins; simpl; intros; [constructor; auto|].
    inv H; destruct a; try (intuition; fail).
    specialize (IHins H3); destruct IHins.
    split.
    - constructor; auto.
      eapply TrsIns; eauto.
    - simpl; rewrite H0 at 1; reflexivity.
  Qed.

  Lemma sequential_outsHistory:
    forall `{oifc: OStateIfc} (sys: System) outs,
      OutsHistory outs ->
      Sequential sys outs (lift_each outs).
  Proof.
    induction outs; simpl; intros; [constructor; auto|].
    inv H; destruct a; try (intuition; fail).
    specialize (IHouts H3); destruct IHouts.
    split.
    - constructor; auto.
      eapply TrsOuts; eauto.
    - simpl; rewrite H0 at 1; reflexivity.
  Qed.

  Lemma ssequential_insHistory:
    forall `{oifc: OStateIfc} (sys: System) ins,
      InsHistory ins ->
      SSequential sys (lift_each ins) 0.
  Proof.
    induction ins; simpl; intros.
    - apply SSeqNil.
    - inv H; destruct a; try (intuition; fail).
      specialize (IHins H3).
      econstructor; eauto.
      eapply STrsIns; reflexivity.
  Qed.

  Lemma ssequential_outsHistory:
    forall `{oifc: OStateIfc} (sys: System) outs,
      OutsHistory outs ->
      SSequential sys (lift_each outs) 0.
  Proof.
    induction outs; simpl; intros.
    - apply SSeqNil.
    - inv H; destruct a; try (intuition; fail).
      specialize (IHouts H3).
      econstructor; eauto.
      eapply STrsOuts; reflexivity.
  Qed.

  Lemma sequential_app:
    forall `{oifc: OStateIfc} (sys: System) ll1 trss1 ll2 trss2,
      Sequential sys ll1 trss1 ->
      Sequential sys ll2 trss2 ->
      Sequential sys (ll1 ++ ll2) (trss1 ++ trss2).
  Proof.
    unfold Sequential; intros.
    destruct H, H0; subst.
    split.
    - apply Forall_app; auto.
    - apply eq_sym, concat_app.
  Qed.

  Lemma sequential_serializable:
    forall `{oifc: OStateIfc} (sys: System) hst trss st,
      steps step_m sys (initsOf sys) hst st ->
      Sequential sys hst trss ->
      Serializable sys st.
  Proof.
    intros; red; intros.
    eexists; split; eauto.
  Qed.

  Lemma stransactional_default:
    forall `{oifc: OStateIfc} (sys: System) lbl,
      exists n,
        STransactional sys [lbl] n.
  Proof.
    destruct lbl; intros; eexists.
    - eapply STrsSlt.
    - eapply STrsIns; eauto.
    - instantiate
        (1:= if subList_dec idx_dec (idsOf mins) sys.(sys_merqs)
             then _ else _).
      destruct (subList_dec idx_dec (idsOf mins) sys.(sys_merqs)).
      + eapply STrsExtAtomic.
        econstructor; eauto.
        econstructor.
      + eapply STrsIntAtomic.
        econstructor; eauto.
        econstructor.
    - eapply STrsOuts; eauto.
  Qed.

  Lemma ssequential_default:
    forall `{oifc: OStateIfc} (sys: System) hst,
    exists n trss,
      SSequential sys trss n /\ hst = List.concat trss.
  Proof.
    induction hst as [|l hst]; simpl; intros; [repeat econstructor; eauto|].
    destruct IHhst as [n [trss ?]]; dest; subst.
    pose proof (stransactional_default sys l).
    destruct H0 as [ln ?].
    exists (ln + n), ([l] :: trss).
    split.
    - econstructor; eauto.
    - reflexivity.
  Qed.

  Lemma ssequential_add:
    forall `{oifc: OStateIfc} (sys: System) ll1 ll2 n,
      SSequential sys (ll1 ++ ll2) n ->
      forall trs tn,
        STransactional sys trs tn ->
        SSequential sys (ll1 ++ trs :: ll2) (tn + n).
  Proof.
    induction ll1; simpl; intros; [econstructor; eauto|].
    inv H; inv H3.
    specialize (IHll1 _ _ H1 _ _ H0).
    econstructor.
    - exact IHll1.
    - exact H2.
    - reflexivity.
    - lia.
  Qed.

  Lemma ssequential_app:
    forall `{oifc: OStateIfc} (sys: System) ll1 n1 ll2 n2,
      SSequential sys ll1 n1 ->
      SSequential sys ll2 n2 ->
      SSequential sys (ll1 ++ ll2) (n1 + n2).
  Proof.
    induction 1; simpl; intros; subst; simpl; auto.
    econstructor.
    - exact (IHSSequential H3).
    - eassumption.
    - reflexivity.
    - lia.
  Qed.

  Lemma ssequential_app_inv:
    forall `{oifc: OStateIfc} (sys: System) ll1 ll2 n,
      SSequential sys (ll1 ++ ll2) n ->
      exists n1 n2,
        SSequential sys ll1 n1 /\
        SSequential sys ll2 n2 /\
        n = n1 + n2.
  Proof.
    induction ll1; simpl; intros.
    - exists 0, n; repeat split; [constructor|assumption].
    - inv H; inv H2.
      specialize (IHll1 _ _ H0).
      destruct IHll1 as [n1 [n2 ?]]; dest; subst.
      exists (tn + n1), n2; repeat split.
      + econstructor.
        * exact H.
        * exact H1.
        * reflexivity.
        * reflexivity.
      + assumption.
      + lia.
  Qed.

  Lemma ssequential_distr_inv:
    forall `{oifc: OStateIfc} (sys: System) ll ll1 ll2,
      Distribution ll ll1 ll2 ->
      forall n,
        SSequential sys ll n ->
        exists n1 n2,
          SSequential sys ll1 n1 /\
          SSequential sys ll2 n2 /\
          n = n1 + n2.
  Proof.
    induction 1; simpl; intros.
    - inv H; try discriminate.
      exists 0, 0; repeat split; constructor.
    - inv H0; inv H3.
      specialize (IHDistribution _ H1).
      destruct IHDistribution as [n1 [n2 ?]]; dest; subst.
      apply ssequential_app_inv in H0.
      destruct H0 as [n11 [n12 ?]]; dest; subst.
      exists (n11 + (tn + n12)), n2; repeat split.
      + apply ssequential_app; auto.
        econstructor; try reflexivity; auto.
      + assumption.
      + lia.
    - inv H0; inv H3.
      specialize (IHDistribution _ H1).
      destruct IHDistribution as [n1 [n2 ?]]; dest; subst.
      apply ssequential_app_inv in H3.
      destruct H3 as [n21 [n22 ?]]; dest; subst.
      exists n1, (n21 + (tn + n22)); repeat split.
      + assumption.
      + apply ssequential_app; auto.
        econstructor; try reflexivity; auto.
      + lia.
  Qed.

  Lemma intAtomic_stransactional_split_each:
    forall `{oifc: OStateIfc} (sys: System) inits ins trs outs eouts,
      ~ SubList (idsOf inits) (sys_merqs sys) ->
      Atomic inits ins trs outs eouts ->
      exists sn,
        SSequential sys (lift_each trs) sn /\
        sn <= List.length trs.
  Proof.
    induction 2; simpl; intros; subst.
    - eexists; split.
      + econstructor; try reflexivity.
        * eapply SSeqNil.
        * eapply STrsIntAtomic.
          econstructor; eauto.
          econstructor.
      + simpl; lia.
    - specialize (IHAtomic H).
      destruct IHAtomic as [sn [? ?]].
      destruct (subList_dec idx_dec (idsOf rins) (sys_merqs sys)).
      + eexists; split.
        * econstructor; try reflexivity.
          { eassumption. }
          { eapply STrsExtAtomic.
            econstructor; eauto.
            econstructor.
          }
        * lia.
      + eexists; split.
        * econstructor; try reflexivity.
          { eassumption. }
          { eapply STrsIntAtomic.
            econstructor; eauto.
            econstructor.
          }
        * simpl; lia.
  Qed.

  Corollary internal_stransactional_split_each:
    forall `{oifc: OStateIfc} (sys: System) inits ins trs outs eouts tn,
      ~ SubList (idsOf inits) (sys_merqs sys) ->
      Atomic inits ins trs outs eouts ->
      STransactional sys trs tn ->
      exists sn,
        SSequential sys (lift_each trs) sn /\
        sn <= tn.
  Proof.
    intros.
    inv H1; try (inv H0; fail).
    - eapply intAtomic_stransactional_split_each; eauto.
    - exfalso; inv H2.
      pose proof (atomic_unique H0 H3); dest; subst.
      auto.
  Qed.

End MsgParam.

Lemma atomic_Transactional_ExtAtomic:
  forall `{dv: DecValue} `{oifc: OStateIfc} (sys: System) trs,
    AtomicEx trs ->
    Transactional sys trs ->
    exists einits eouts,
      ExtAtomic sys einits trs eouts.
Proof.
  intros.
  destruct H as [inits [ins [outs [eouts ?]]]].
  inv H0; try (inv H; fail).
  eauto.
Qed.

Lemma sequential_transactional_Forall:
  forall `{dv: DecValue} `{oifc: OStateIfc} (sys: System) st1 trss st2,
    steps step_m sys st1 (List.concat trss) st2 ->
    Forall (Transactional sys) trss ->
    Sequential sys (List.concat trss) trss.
Proof.
  induction trss; simpl; intros; [repeat constructor|].
  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  inv H0.
  eapply sequential_cons; eauto.
Qed.

Lemma atomic_messages_eouts_count_le:
  forall `{dv: DecValue} inits ins hst outs eouts,
    Atomic inits ins hst outs eouts ->
    forall `{oifc: OStateIfc} (sys: System) st1 st2,
      steps step_m sys st1 hst st2 ->
      forall idm,
        count_occ (id_dec msg_dec) eouts idm <=
        countMsg msg_dec idm st2.(st_msgs).
Proof.
  induction 1; simpl; intros; subst.
  - inv_steps; inv_step; simpl.
    rewrite countMsg_enqMsgs; lia.
  - inv_steps; inv_step; simpl.
    rewrite count_occ_app, countMsg_enqMsgs.
    specialize (IHAtomic _ _ _ _ H6 idm); simpl in IHAtomic.
    destruct H14.
    assert (NoDup rins) by (apply idsOf_NoDup in H3; auto).
    pose proof (countMsg_deqMsgs msg_dec idm H3 H13).
    pose proof (count_occ_removeL (id_dec msg_dec) idm H1 H4).
    lia.
Qed.

Lemma atomic_messages_eouts_in:
  forall `{dv: DecValue} inits ins hst outs eouts,
    Atomic inits ins hst outs eouts ->
    forall `{oifc: OStateIfc} (sys: System) st1 st2,
      steps step_m sys st1 hst st2 ->
      Forall (InMPI st2.(st_msgs)) eouts.
Proof.
  intros.
  apply Forall_forall; intros idm ?.
  apply (countMsg_InMPI msg_dec).
  eapply atomic_messages_eouts_count_le with (idm0:= idm) in H; eauto.
  apply (count_occ_In (id_dec msg_dec)) in H1.
  lia.
Qed.

Lemma atomic_messages_non_inits_count_eq:
  forall `{dv: DecValue} inits ins hst outs eouts,
    Atomic inits ins hst outs eouts ->
    forall `{oifc: OStateIfc} (sys: System) st1 st2,
      steps step_m sys st1 hst st2 ->
      forall idm,
        ~ In idm inits ->
        countMsg msg_dec idm (st_msgs st1) +
        count_occ (id_dec msg_dec) eouts idm =
        countMsg msg_dec idm (st_msgs st2).
Proof.
  induction 1; simpl; intros; subst.
  - inv_steps; inv_step; simpl.
    rewrite countMsg_enqMsgs.
    destruct H11.
    pose proof (countMsg_deqMsgs msg_dec idm H1 H10).
    rewrite (count_occ_not_In (id_dec msg_dec)) in H0.
    lia.
  - inv_steps; inv_step; simpl.
    rewrite count_occ_app, countMsg_enqMsgs.
    rewrite Nat.add_assoc.
    specialize (IHAtomic _ _ _ _ H7 _ H6); simpl in IHAtomic.
    destruct H15.
    assert (NoDup rins) by (apply idsOf_NoDup in H3; auto).
    pose proof (countMsg_deqMsgs msg_dec idm H3 H14).
    pose proof (count_occ_removeL (id_dec msg_dec) idm H1 H4).
    lia.
Qed.

Lemma atomic_messages_in_in:
  forall `{dv: DecValue} inits ins hst outs eouts,
    Atomic inits ins hst outs eouts ->
    forall `{oifc: OStateIfc} (sys: System) st1 st2,
      steps step_m sys st1 hst st2 ->
      forall idm,
        InMPI (st_msgs st1) idm ->
        ~ In idm inits ->
        InMPI (st_msgs st2) idm.
Proof.
  intros.
  apply (countMsg_InMPI msg_dec) in H1.
  apply (countMsg_InMPI msg_dec).
  pose proof (atomic_messages_non_inits_count_eq H H0 _ H2).
  lia.
Qed.

Corollary atomic_messages_ins_ins:
  forall `{dv: DecValue} inits ins hst outs eouts,
    Atomic inits ins hst outs eouts ->
    forall `{oifc: OStateIfc} (sys: System) st1 st2,
      steps step_m sys st1 hst st2 ->
      forall msgs,
        Forall (InMPI (st_msgs st1)) msgs ->
        DisjList inits msgs ->
        Forall (InMPI (st_msgs st2)) msgs.
Proof.
  intros.
  rewrite Forall_forall in H1.
  apply Forall_forall; intros idm ?.
  eapply atomic_messages_in_in; eauto.
  destruct (H2 idm); auto.
Qed.

Lemma atomic_non_inits_InMPI_or:
  forall `{dv: DecValue} inits ins hst outs eouts,
    Atomic inits ins hst outs eouts ->
    forall `{oifc: OStateIfc} (sys: System) st1 st2,
      steps step_m sys st1 hst st2 ->
      forall idm,
        ~ In idm inits ->
        InMPI st2.(st_msgs) idm ->
        InMPI st1.(st_msgs) idm \/ In idm eouts.
Proof.
  intros.
  eapply atomic_messages_non_inits_count_eq in H; [|eassumption..].
  apply (countMsg_InMPI msg_dec) in H2.
  assert (countMsg msg_dec idm st1.(st_msgs) > 0 \/
          count_occ (id_dec msg_dec) eouts idm > 0) by lia.
  destruct H3.
  - left; apply (countMsg_InMPI msg_dec); assumption.
  - right; apply (count_occ_In (id_dec msg_dec)); assumption.
Qed.

Lemma extAtomic_non_inits_InMPI_or:
  forall `{dv: DecValue} `{oifc: OStateIfc} (sys: System) inits hst eouts,
    ExtAtomic sys inits hst eouts ->
    forall st1 st2,
      steps step_m sys st1 hst st2 ->
      forall idm,
        ~ In (idOf idm) (sys_merqs sys) ->
        InMPI st2.(st_msgs) idm ->
        InMPI st1.(st_msgs) idm \/ In idm eouts.
Proof.
  intros.
  inv H.
  eapply atomic_non_inits_InMPI_or; try eassumption.
  intro Hx.
  apply in_map with (f:= idOf) in Hx.
  apply H3 in Hx; auto.
Qed.

Lemma extAtomic_multi_non_inits_InMPI_or:
  forall `{dv: DecValue} `{oifc: OStateIfc} (sys: System) st1,
    Reachable (steps step_m) sys st1 ->
    forall trss st2,
      steps step_m sys st1 (List.concat trss) st2 ->
      Forall AtomicEx trss ->
      Forall (Transactional sys) trss ->
      forall idm,
        ~ In (idOf idm) (sys_merqs sys) ->
        InMPI st2.(st_msgs) idm ->
        InMPI st1.(st_msgs) idm \/
        exists einits trs eouts,
          In trs trss /\
          ExtAtomic sys einits trs eouts /\
          In idm eouts.
Proof.
  induction trss as [|trs trss]; simpl; intros; [inv_steps; auto|].

  eapply steps_split in H0; [|reflexivity].
  destruct H0 as [sti [? ?]].
  inv H1; inv H2.
  pose proof (atomic_Transactional_ExtAtomic H8 H7).
  destruct H1 as [einits [eouts ?]].

  eapply extAtomic_non_inits_InMPI_or in H5; try eassumption.
  destruct H5; [|eauto 8].

  specialize (IHtrss _ H0 H9 H10 _ H3 H2).
  destruct IHtrss; [auto|].
  destruct H5 as [teinits [ttrs [teouts ?]]]; dest.
  right; eauto 7.
Qed.

Corollary extAtomic_multi_IntMsgsEmpty_non_inits_InMPI:
  forall `{dv: DecValue} `{oifc: OStateIfc} (sys: System) st1,
    Reachable (steps step_m) sys st1 ->
    IntMsgsEmpty sys st1.(st_msgs) ->
    forall trss st2,
      steps step_m sys st1 (List.concat trss) st2 ->
      Forall AtomicEx trss ->
      Forall (Transactional sys) trss ->
      forall idm,
        In (idOf idm) (sys_minds sys) ->
        InMPI st2.(st_msgs) idm ->
        exists einits trs eouts,
          In trs trss /\
          ExtAtomic sys einits trs eouts /\
          In idm eouts.
Proof.
  intros.
  eapply extAtomic_multi_non_inits_InMPI_or in H1; try eassumption.
  - destruct H1; [|assumption].
    exfalso.
    specialize (H0 _ H4).
    apply findQ_length_ge_one in H1.
    rewrite H0 in H1; simpl in H1; lia.
  - eapply DisjList_In_2.
    + eapply sys_minds_sys_merqs_DisjList.
    + assumption.
Qed.

Lemma insLbl_IntMsgsEmpty:
  forall `{dv: DecValue} `{oifc: OStateIfc} (sys: System) st1 lbl st2,
    step_m sys st1 lbl st2 ->
    IntMsgsEmpty sys st1.(st_msgs) ->
    InsLbl lbl ->
    IntMsgsEmpty sys st2.(st_msgs).
Proof.
  intros; red in H1.
  inv H; try (exfalso; auto; fail).
  simpl in *.
  red in H3; dest.
  red in H0; red; intros.
  specialize (H0 _ H4).
  rewrite findQ_not_In_enqMsgs.
  - assumption.
  - intro Hx; apply H in Hx.
    destruct (sys_minds_sys_merqs_DisjList sys midx); auto.
Qed.

Lemma insHistory_IntMsgsEmpty:
  forall `{dv: DecValue} `{oifc: OStateIfc} (sys: System) st1 hst st2,
    steps step_m sys st1 hst st2 ->
    IntMsgsEmpty sys st1.(st_msgs) ->
    InsHistory hst ->
    IntMsgsEmpty sys st2.(st_msgs).
Proof.
  induction 1; simpl; intros; auto.
  inv H2.
  eapply insLbl_IntMsgsEmpty; eauto.
Qed.

Lemma atomic_legal_eouts:
  forall `{dv: DecValue} (hst: History) inits ins outs eouts,
    Atomic inits ins hst outs eouts ->
    forall `{oifc: OStateIfc} (sys: System) st1 st2,
      steps step_m sys st1 hst st2 ->
      (forall nouts,
          removeL (id_dec msg_dec) (inits ++ outs ++ nouts) ins =
          removeL (id_dec msg_dec) (inits ++ outs) ins ++ nouts) /\
      eouts = removeL (id_dec msg_dec) (inits ++ outs) ins.
Proof.
  induction 1; simpl; intros; subst.
  - split.
    + intros.
      do 2 rewrite removeL_app_2.
      reflexivity.
    + rewrite removeL_app_2; reflexivity.
  - inv H5.
    specialize (IHAtomic _ _ _ _ H6).
    assert (NoDup rins) by (inv H8; destruct H14; apply idsOf_NoDup; auto).
    dest; subst; split.
    + intros.
      do 2 rewrite removeL_app_1.
      rewrite <-app_assoc.
      do 2 rewrite H3.
      do 2 (rewrite removeL_app_3 with (l3:= rins) by assumption).
      apply app_assoc.
    + rewrite removeL_app_1.
      rewrite H3.
      rewrite removeL_app_3 with (l3:= rins) by assumption.
      reflexivity.
Qed.

Lemma atomic_eouts_not_erqs:
  forall `{dv: DecValue} inits ins hst outs eouts,
    Atomic inits ins hst outs eouts ->
    forall `{oifc: OStateIfc} (sys: System) st1 st2,
      steps step_m sys st1 hst st2 ->
      Forall (fun eout => ~ In (idOf eout) sys.(sys_merqs)) eouts.
Proof.
  induction 1; simpl; intros; subst.
  - inv_steps; inv_step.
    destruct H14.
    apply Forall_forall; intros [midx msg] ?.
    apply in_map with (f:= idOf) in H1.
    simpl in *.
    apply H in H1.
    eapply DisjList_In_2; [|eassumption].
    apply DisjList_app_4.
    + apply sys_minds_sys_merqs_DisjList.
    + apply DisjList_comm, sys_merqs_sys_merss_DisjList.
  - inv_steps.
    apply Forall_app; [apply forall_removeL; eauto|].
    inv_step.
    destruct H18.
    apply Forall_forall; intros [midx msg] ?.
    apply in_map with (f:= idOf) in H4.
    simpl in *.
    apply H2 in H4.
    eapply DisjList_In_2; [|eassumption].
    apply DisjList_app_4.
    + apply sys_minds_sys_merqs_DisjList.
    + apply DisjList_comm, sys_merqs_sys_merss_DisjList.
Qed.

Lemma atomic_inits_in:
  forall `{dv: DecValue} inits ins hst outs eouts,
    Atomic inits ins hst outs eouts ->
    SubList inits ins.
Proof.
  induction 1; simpl; intros; subst;
    [apply SubList_refl|].
  apply SubList_app_1; auto.
Qed.

Lemma atomic_eouts_in:
  forall `{dv: DecValue} inits ins hst outs eouts,
    Atomic inits ins hst outs eouts ->
    SubList eouts outs.
Proof.
  induction 1; simpl; intros; subst;
    [apply SubList_refl|].
  apply SubList_app_3.
  - eapply SubList_trans.
    + apply removeL_SubList_2.
    + apply SubList_app_1; auto.
  - apply SubList_app_2, SubList_refl.
Qed.

Lemma atomic_outs_cases:
  forall `{dv: DecValue} inits ins hst outs eouts,
    Atomic inits ins hst outs eouts ->
    forall msg,
      In msg outs -> In msg eouts \/ In msg ins.
Proof.
  induction 1; simpl; intros; subst; auto.

  apply in_app_or in H5; destruct H5.
  - specialize (IHAtomic _ H2); destruct IHAtomic.
    + destruct (in_dec (id_dec msg_dec) msg rins).
      * right; apply in_or_app; auto.
      * left; apply in_or_app; left.
        apply removeL_In_1; auto.
    + right; apply in_or_app; auto.
  - left; apply in_or_app; auto.
Qed.

Lemma atomic_ins_cases:
  forall `{dv: DecValue} inits ins hst outs eouts,
    Atomic inits ins hst outs eouts ->
    forall msg,
      In msg ins -> In msg inits \/ In msg outs.
Proof.
  induction 1; simpl; intros; subst; auto.

  apply in_app_or in H5; destruct H5.
  - specialize (IHAtomic _ H2); destruct IHAtomic; auto.
    right; apply in_or_app; auto.
  - apply H1 in H2.
    pose proof (atomic_eouts_in H).
    apply H3 in H2.
    right; apply in_or_app; auto.
Qed.

Lemma atomic_app_SSubList:
  forall `{dv: DecValue} (hst1: History) inits1 ins1 outs1 eouts1,
    Atomic inits1 ins1 hst1 outs1 eouts1 ->
    forall hst2 inits2 ins2 outs2 eouts2,
      inits2 <> nil ->
      Atomic inits2 ins2 hst2 outs2 eouts2 ->
      SubList inits2 eouts1 ->
      exists eouts,
        SSubList eouts2 eouts /\
        Atomic inits1 (ins1 ++ ins2)
               (hst2 ++ hst1)
               (outs1 ++ outs2)
               eouts.
Proof.
  induction 3; simpl; intros.
  - eexists; split; [|econstructor; eauto].
    apply SSubList_app_1.
  - subst.
    specialize (IHAtomic H0 H7).
    destruct IHAtomic as [peouts [? ?]].

    eexists; split;
      [|apply SSubList_SubList in H4;
        do 2 rewrite app_assoc;
        econstructor; eauto;
        eapply SubList_trans; eauto].

    apply SSubList_app_2.
    apply SSubList_removeL_2; auto.
Qed.

Corollary atomic_app:
  forall `{dv: DecValue} (hst1: History) inits1 ins1 outs1 eouts1,
    Atomic inits1 ins1 hst1 outs1 eouts1 ->
    forall hst2 inits2 ins2 outs2 eouts2,
      inits2 <> nil ->
      Atomic inits2 ins2 hst2 outs2 eouts2 ->
      SubList inits2 eouts1 ->
      exists eouts,
        Atomic inits1 (ins1 ++ ins2)
               (hst2 ++ hst1)
               (outs1 ++ outs2)
               eouts.
Proof.
  intros.
  pose proof (atomic_app_SSubList H H0 H1 H2).
  dest; eauto.
Qed.
