Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap.
Require Import Syntax Semantics SemFacts StepM Serial Invariant.

Require Import Omega.
Require Import Program.Equality.

Set Implicit Arguments.

Open Scope list.

Section MsgParam.
  Variable MsgT: Type.
  Hypothesis (msgT_dec : forall m1 m2 : MsgT, {m1 = m2} + {m1 <> m2}).

  Lemma atomic_emptyILabel_not_in:
    forall inits ins hst outs eouts,
      Atomic msgT_dec inits ins hst outs eouts ->
      ~ In (RlblEmpty MsgT) hst.
  Proof.
    induction 1; simpl; intros.
    - intro Hx; destruct Hx; [discriminate|auto].
    - intro Hx; destruct Hx; subst; [discriminate|auto].
  Qed.

  Lemma atomic_iLblIn_not_in:
    forall inits ins hst outs eouts,
      Atomic msgT_dec inits ins hst outs eouts ->
      forall msg, ~ In (RlblIns [msg]) hst.
  Proof.
    induction 1; simpl; intros; [auto|];
      try (intro Hx; destruct Hx;
           [discriminate|firstorder]).
  Qed.

  Fixpoint insOfA (hst: History MsgT) :=
    match hst with
    | nil => nil
    | lbl :: hst' =>
      match lbl with
      | RlblInt _ _ ins _ => insOfA hst' ++ ins
      | _ => nil
      end
    end.

  Fixpoint outsOfA (hst: History MsgT) :=
    match hst with
    | nil => nil
    | lbl :: hst' =>
      match lbl with
      | RlblInt _ _ _ outs => outsOfA hst' ++ outs
      | _ => nil
      end
    end.

  Lemma atomic_ins:
    forall (hst: History MsgT) inits ins outs eouts,
      Atomic msgT_dec inits ins hst outs eouts ->
      ins = insOfA hst.
  Proof.
    induction 1; simpl; intros; subst; reflexivity.
  Qed.

  Lemma atomic_outs:
    forall (hst: History MsgT) inits ins outs eouts,
      Atomic msgT_dec inits ins hst outs eouts ->
      outs = outsOfA hst.
  Proof.
    induction 1; simpl; intros; subst; reflexivity.
  Qed.

  Lemma atomic_unique:
    forall (hst: History MsgT) inits1 ins1 outs1 eouts1,
      Atomic msgT_dec inits1 ins1 hst outs1 eouts1 ->
      forall inits2 ins2 outs2 eouts2,
        Atomic msgT_dec inits2 ins2 hst outs2 eouts2 ->
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
      Atomic msg_dec inits ins hst outs eouts ->
      forall {oifc} (sys: System oifc) st1 st2,
        steps step_m sys st1 hst st2 ->
        bst_msgs st2 = deqMsgs (idsOf ins) (enqMsgs outs (bst_msgs st1)) /\
        ValidDeqs (enqMsgs outs (bst_msgs st1)) (idsOf ins).
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
      Atomic msg_dec inits ins hst outs eouts ->
      forall {oifc} (sys: System oifc) st1 st2,
        steps step_m sys st1 hst st2 ->
        bst_msgs st2 = deqMsgs (idsOf ins) (enqMsgs outs (bst_msgs st1)).
  Proof.
    intros; eapply atomic_messages_spec_ValidDeqs; eauto.
  Qed.

  Lemma atomic_messages_ins_outs:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
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

  Lemma atomic_messages_eouts_in:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall {oifc} (sys: System oifc) st1 st2,
        steps step_m sys st1 hst st2 ->
        Forall (InMPI st2.(bst_msgs)) eouts.
  Proof.
    (* induction 1; simpl; intros. *)
    (* - inv_steps; inv_step; simpl in *. *)
    (*   destruct H14. *)
    (*   apply Forall_forall; intros [midx msg] ?. *)
    (*   admit. *)
    (* - inv_steps; inv_step; simpl in *. *)
    (*   apply Forall_app. *)
    (*   + specialize (IHAtomic _ _ _ _ H9); simpl in IHAtomic. *)
    (*     destruct H14; red in H3. *)
    (*     clear -IHAtomic H3. *)
    (*     admit. *)
    (*   + destruct H18. *)
    (*     apply Forall_forall; intros [midx msg] ?. *)
    (*     admit. *)
  Admitted.

  Lemma atomic_messages_in_in:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall {oifc} (sys: System oifc) st1 st2,
        steps step_m sys st1 hst st2 ->
        forall idm,
          InMPI (bst_msgs st1) idm ->
          ~ In idm inits ->
          InMPI (bst_msgs st2) idm.
  Proof.
    (* intros. *)
    (* pose proof (atomic_messages_spec H H0). *)
    (* pose proof (atomic_messages_ins_outs H). *)
    (* destruct (in_dec (id_dec msg_dec) idm outs). *)

    (* induction 1; simpl; intros; subst. *)

    (* - inv H; inv H5. *)
    (*   eapply internal_transition_messages_in; eauto. *)

    (* - inv H5. *)
    (*   specialize (IHAtomic _ _ _ _ H8 _ H6 H7). *)
    (*   destruct (in_dec (id_dec msg_dec) idm rins); *)
    (*     [|eauto using internal_transition_messages_in]. *)

    (*   apply H1 in i. *)
    (*   assert (In idm outs). *)
    (*   { pose proof (atomic_messages_ins_outs H). *)
    (*     destruct H2. *)
    (*     assert (In idm (ins ++ eouts)) by (apply in_or_app; auto). *)
    (*     apply H3 in H4. *)
    (*     apply in_app_or in H4. *)
    (*     destruct H4; intuition. *)
    (*   } *)
  Admitted.

  Corollary atomic_messages_ins_ins:
    forall inits ins hst outs eouts,
      Atomic msg_dec inits ins hst outs eouts ->
      forall {oifc} (sys: System oifc) st1 st2,
        steps step_m sys st1 hst st2 ->
        forall msgs,
          Forall (InMPI (bst_msgs st1)) msgs ->
          DisjList inits msgs ->
          Forall (InMPI (bst_msgs st2)) msgs.
  Proof.
    intros.
    rewrite Forall_forall in H1.
    apply Forall_forall; intros idm ?.
    eapply atomic_messages_in_in; eauto.
    destruct (H2 idm); auto.
  Qed.
  
  Lemma atomic_behavior_nil:
    forall `{HasMsg MsgT} (hst: History MsgT) inits ins outs eouts,
      Atomic msgT_dec inits ins hst outs eouts ->
      behaviorOf hst = nil.
  Proof.
    induction 1; simpl; intros; auto.
  Qed.

  Lemma atomic_singleton:
    forall oidx ridx ins outs,
      Atomic msgT_dec ins ins [RlblInt oidx ridx ins outs] outs outs.
  Proof.
    intros; constructor.
  Qed.

  Lemma extAtomic_preserved:
    forall {oifc} (impl1: System oifc) hst eouts,
      ExtAtomic impl1 msgT_dec hst eouts ->
      forall (impl2: System oifc),
        sys_merqs impl1 = sys_merqs impl2 ->
        ExtAtomic impl2 msgT_dec hst eouts.
  Proof.
    intros.
    inv H.
    econstructor; eauto.
    rewrite <-H0; assumption.
  Qed.

  Lemma atomic_split_each:
    forall inits ins hst outs eouts,
      Atomic msgT_dec inits ins hst outs eouts ->
      Forall (AtomicEx msgT_dec) (lift_each hst).
  Proof.
    induction 1; simpl; intros; [repeat econstructor|].
    repeat econstructor.
    assumption.
  Qed.

  Lemma atomicEx_split_each:
    forall hst,
      AtomicEx msgT_dec hst ->
      Forall (AtomicEx msgT_dec) (lift_each hst).
  Proof.
    unfold AtomicEx; intros; dest.
    eapply atomic_split_each; eauto.
  Qed.

  Definition InternalLbl (lbl: RLabel MsgT) :=
    match lbl with
    | RlblInt _ _ _ _ => True
    | _ => False
    end.

  Definition InsLbl (lbl: RLabel MsgT) :=
    match lbl with
    | RlblIns _ => True
    | _ => False
    end.

  Definition OutsLbl (lbl: RLabel MsgT) :=
    match lbl with
    | RlblOuts _ => True
    | _ => False
    end.

  Definition NonInsLbl (lbl: RLabel MsgT) :=
    match lbl with
    | RlblIns _ => False
    | _ => True
    end.

  Definition NonOutsLbl (lbl: RLabel MsgT) :=
    match lbl with
    | RlblOuts _ => False
    | _ => True
    end.

  Definition HistoryP (P: RLabel MsgT -> Prop) (hst: History MsgT) :=
    Forall (fun lbl => P lbl) hst.

  Definition InternalHistory := HistoryP InternalLbl.
  Definition InsHistory := HistoryP InsLbl.
  Definition OutsHistory := HistoryP OutsLbl.
  Definition NonInsHistory := HistoryP NonInsLbl.
  Definition NonOutsHistory := HistoryP NonOutsLbl.

  Lemma atomic_internal_history:
    forall inits ins hst outs eouts,
      Atomic msgT_dec inits ins hst outs eouts ->
      InternalHistory hst.
  Proof.
    induction 1; simpl; intros.
    - repeat constructor.
    - repeat constructor; auto.
  Qed.

  Lemma atomicEx_internal_history:
    forall hst,
      AtomicEx msgT_dec hst ->
      InternalHistory hst.
  Proof.
    unfold AtomicEx; intros; dest.
    eapply atomic_internal_history; eauto.
  Qed.
  
  Lemma sequential_nil:
    forall {oifc} (sys: System oifc), Sequential sys msgT_dec nil nil.
  Proof.
    intros; hnf; intros.
    split.
    - constructor.
    - reflexivity.
  Qed.

  Lemma sequential_cons:
    forall {oifc} (sys: System oifc) ll trss,
      Sequential sys msgT_dec ll trss ->
      forall trs,
        Transactional sys msgT_dec trs ->
        Sequential sys msgT_dec (trs ++ ll) (trs :: trss).
  Proof.
    intros.
    inv H.
    constructor; auto.
  Qed.

  Lemma sequential_silent:
    forall {oifc} (sys: System oifc) ll trss,
      Sequential sys msgT_dec ll trss ->
      Sequential sys msgT_dec (RlblEmpty _ :: ll) ([RlblEmpty _] :: trss).
  Proof.
    intros.
    hnf; hnf in H; dest.
    split.
    - constructor; [|eassumption].
      constructor.
    - subst; reflexivity.
  Qed.

  Lemma sequential_msg_ins:
    forall {oifc} (sys: System oifc) ll trss eins,
      Sequential sys msgT_dec ll trss ->
      Sequential sys msgT_dec (RlblIns eins :: ll) ([RlblIns eins] :: trss).
  Proof.
    intros.
    hnf; hnf in H; dest.
    split.
    - constructor; [|eassumption].
      eapply TrsIns; reflexivity.
    - subst; reflexivity.
  Qed.

  Lemma sequential_msg_outs:
    forall {oifc} (sys: System oifc) ll trss eouts,
      Sequential sys msgT_dec ll trss ->
      Sequential sys msgT_dec (RlblOuts eouts :: ll) ([RlblOuts eouts] :: trss).
  Proof.
    intros.
    hnf; hnf in H; dest.
    split.
    - constructor; [|eassumption].
      eapply TrsOuts; reflexivity.
    - subst; reflexivity.
  Qed.

  Lemma sequential_insHistory:
    forall {oifc} (sys: System oifc) ins,
      InsHistory ins ->
      Sequential sys msgT_dec ins (lift_each ins).
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
    forall {oifc} (sys: System oifc) outs,
      OutsHistory outs ->
      Sequential sys msgT_dec outs (lift_each outs).
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
    forall {oifc} (sys: System oifc) ins,
      InsHistory ins ->
      SSequential sys msgT_dec (lift_each ins) 0.
  Proof.
    induction ins; simpl; intros.
    - apply SSeqNil.
    - inv H; destruct a; try (intuition; fail).
      specialize (IHins H3).
      econstructor; eauto.
      eapply STrsIns; reflexivity.
  Qed.

  Lemma ssequential_outsHistory:
    forall {oifc} (sys: System oifc) outs,
      OutsHistory outs ->
      SSequential sys msgT_dec (lift_each outs) 0.
  Proof.
    induction outs; simpl; intros.
    - apply SSeqNil.
    - inv H; destruct a; try (intuition; fail).
      specialize (IHouts H3).
      econstructor; eauto.
      eapply STrsOuts; reflexivity.
  Qed.

  Lemma sequential_app:
    forall {oifc} (sys: System oifc) ll1 trss1 ll2 trss2,
      Sequential sys msgT_dec ll1 trss1 ->
      Sequential sys msgT_dec ll2 trss2 ->
      Sequential sys msgT_dec (ll1 ++ ll2) (trss1 ++ trss2).
  Proof.
    unfold Sequential; intros.
    destruct H, H0; subst.
    split.
    - apply Forall_app; auto.
    - apply eq_sym, concat_app.
  Qed.

  Lemma sequential_serializable:
    forall {oifc} (sys: System oifc) hst trss st,
      steps step_m sys (initsOf sys) hst st ->
      Sequential sys msg_dec hst trss ->
      Serializable sys hst st.
  Proof.
    intros; red; intros.
    eexists; split; eauto.
  Qed.

  Lemma stransactional_default:
    forall {oifc} (sys: System oifc) lbl,
      exists n,
        STransactional sys msgT_dec [lbl] n.
  Proof.
    destruct lbl; intros; eexists.
    - eapply STrsSlt.
    - eapply STrsIns; eauto.
    - instantiate
        (1:= if subList_dec eq_nat_dec (idsOf mins) sys.(sys_merqs)
             then _ else _).
      destruct (subList_dec eq_nat_dec (idsOf mins) sys.(sys_merqs)).
      + eapply STrsExtAtomic.
        econstructor; eauto.
        econstructor.
      + eapply STrsIntAtomic.
        econstructor; eauto.
        econstructor.
    - eapply STrsOuts; eauto.
  Qed.

  Lemma ssequential_default:
    forall {oifc} (sys: System oifc) hst,
    exists n trss,
      SSequential sys msgT_dec trss n /\ hst = List.concat trss.
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
    forall {oifc} (sys: System oifc) ll1 ll2 n,
      SSequential sys msgT_dec (ll1 ++ ll2) n ->
      forall trs tn,
        STransactional sys msgT_dec trs tn ->
        SSequential sys msgT_dec (ll1 ++ trs :: ll2) (tn + n).
  Proof.
    induction ll1; simpl; intros; [econstructor; eauto|].
    inv H; inv H3.
    specialize (IHll1 _ _ H1 _ _ H0).
    econstructor.
    - exact IHll1.
    - exact H2.
    - reflexivity.
    - omega.
  Qed.
  
  Lemma ssequential_app:
    forall {oifc} (sys: System oifc) ll1 n1 ll2 n2,
      SSequential sys msgT_dec ll1 n1 ->
      SSequential sys msgT_dec ll2 n2 ->
      SSequential sys msgT_dec (ll1 ++ ll2) (n1 + n2).
  Proof.
    induction 1; simpl; intros; subst; simpl; auto.
    econstructor.
    - exact (IHSSequential H3).
    - eassumption.
    - reflexivity.
    - omega.
  Qed.

  Lemma ssequential_app_inv:
    forall {oifc} (sys: System oifc) ll1 ll2 n,
      SSequential sys msgT_dec (ll1 ++ ll2) n ->
      exists n1 n2,
        SSequential sys msgT_dec ll1 n1 /\
        SSequential sys msgT_dec ll2 n2 /\
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
      + omega.
  Qed.

  Lemma ssequential_distr_inv:
    forall {oifc} (sys: System oifc) ll ll1 ll2,
      Distribution ll ll1 ll2 ->
      forall n,
        SSequential sys msgT_dec ll n ->
        exists n1 n2,
          SSequential sys msgT_dec ll1 n1 /\
          SSequential sys msgT_dec ll2 n2 /\
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
      + omega.
    - inv H0; inv H3.
      specialize (IHDistribution _ H1).
      destruct IHDistribution as [n1 [n2 ?]]; dest; subst.
      apply ssequential_app_inv in H3.
      destruct H3 as [n21 [n22 ?]]; dest; subst.
      exists n1, (n21 + (tn + n22)); repeat split.
      + assumption.
      + apply ssequential_app; auto.
        econstructor; try reflexivity; auto.
      + omega.
  Qed.

  Lemma intAtomic_stransactional_split_each:
    forall {oifc} (sys: System oifc) inits ins trs outs eouts,
      ~ SubList (idsOf inits) (sys_merqs sys) ->
      Atomic msgT_dec inits ins trs outs eouts ->
      exists sn,
        SSequential sys msgT_dec (lift_each trs) sn /\
        sn <= List.length trs.
  Proof.
    induction 2; simpl; intros; subst.
    - eexists; split.
      + econstructor; try reflexivity.
        * eapply SSeqNil.
        * eapply STrsIntAtomic.
          econstructor; eauto.
          econstructor.
      + simpl; omega.
    - specialize (IHAtomic H).
      destruct IHAtomic as [sn [? ?]].
      destruct (subList_dec eq_nat_dec (idsOf rins) (sys_merqs sys)).
      + eexists; split.
        * econstructor; try reflexivity.
          { eassumption. }
          { eapply STrsExtAtomic.
            econstructor; eauto.
            econstructor.
          }
        * omega.
      + eexists; split.
        * econstructor; try reflexivity.
          { eassumption. }
          { eapply STrsIntAtomic.
            econstructor; eauto.
            econstructor.
          }
        * simpl; omega.
  Qed.

  Corollary internal_stransactional_split_each:
    forall {oifc} (sys: System oifc) inits ins trs outs eouts tn,
      ~ SubList (idsOf inits) (sys_merqs sys) ->
      Atomic msgT_dec inits ins trs outs eouts ->
      STransactional sys msgT_dec trs tn ->
      exists sn,
        SSequential sys msgT_dec (lift_each trs) sn /\
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

Lemma atomic_legal_eouts:
  forall (hst: MHistory) inits ins outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
    forall {oifc} (sys: System oifc) st1 st2,
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

Lemma atomic_inits_in:
  forall inits ins hst outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
    SubList inits ins.
Proof.
  induction 1; simpl; intros; subst;
    [apply SubList_refl|].
  apply SubList_app_1; auto.
Qed.
  
Lemma atomic_eouts_in:
  forall inits ins hst outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
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
  forall inits ins hst outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
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
  forall inits ins hst outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
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
  forall (hst1: MHistory) inits1 ins1 outs1 eouts1,
    Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
    forall hst2 inits2 ins2 outs2 eouts2,
      inits2 <> nil ->
      Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
      SubList inits2 eouts1 ->
      exists eouts,
        SSubList eouts2 eouts /\
        Atomic msg_dec inits1 (ins1 ++ ins2)
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
  forall (hst1: MHistory) inits1 ins1 outs1 eouts1,
    Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
    forall hst2 inits2 ins2 outs2 eouts2,
      inits2 <> nil ->
      Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
      SubList inits2 eouts1 ->
      exists eouts,
        Atomic msg_dec inits1 (ins1 ++ ins2)
               (hst2 ++ hst1)
               (outs1 ++ outs2)
               eouts.
Proof.
  intros.
  pose proof (atomic_app_SSubList H H0 H1 H2).
  dest; eauto.
Qed.

Lemma serializable_nil:
  forall {oifc} (sys: System oifc), Serializable sys nil (initsOf sys).
Proof.
  intros; hnf; intros.
  exists nil; split.
  - constructor.
  - exists nil; constructor; auto.
Qed.

Lemma serializable_silent:
  forall {oifc} (sys: System oifc) ll st,
    Serializable sys ll st ->
    Serializable sys (RlblEmpty _ :: ll) st.
Proof.
  intros.
  hnf; hnf in H; intros; dest.
  destruct H; dest.
  eexists; split; eauto.
Qed.

Close Scope list.

