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
      forall sys st1 st2,
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
      specialize (IHAtomic _ _ _ H6); dest.
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
      forall sys st1 st2,
        steps step_m sys st1 hst st2 ->
        bst_msgs st2 = deqMsgs (idsOf ins) (enqMsgs outs (bst_msgs st1)).
  Proof.
    intros; eapply atomic_messages_spec_ValidDeqs; eauto.
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
    forall impl1 hst,
      ExtAtomic impl1 msgT_dec hst ->
      forall impl2,
        sys_merqs impl1 = sys_merqs impl2 ->
        ExtAtomic impl2 msgT_dec hst.
  Proof.
    intros.
    inv H.
    - eapply ExtAtomicNil; eauto.
    - eapply ExtAtomicSingle; eauto.
      rewrite <-H0; assumption.
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
    forall sys, Sequential sys msgT_dec nil nil.
  Proof.
    intros; hnf; intros.
    split.
    - constructor.
    - reflexivity.
  Qed.

  Lemma sequential_silent:
    forall sys ll trss,
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
    forall sys ll trss eins,
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
    forall sys ll trss eouts,
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
    forall sys ins,
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
    forall sys outs,
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
    forall ins,
      InsHistory ins ->
      SSequential msgT_dec ins (List.length ins).
  Proof.
    induction ins; simpl; intros.
    - apply SSeqIntro with (trss:= nil); auto.
    - inv H; destruct a; try (intuition; fail).
      specialize (IHins H3); inv IHins.
      econstructor.
      + instantiate (1:= [RlblIns mins] :: trss); reflexivity.
      + simpl; rewrite H0; reflexivity.
      + constructor; auto.
        eapply STrsIns; reflexivity.
  Qed.

  Lemma ssequential_outsHistory:
    forall outs,
      OutsHistory outs ->
      SSequential msgT_dec outs (List.length outs).
  Proof.
    induction outs; simpl; intros.
    - apply SSeqIntro with (trss:= nil); auto.
    - inv H; destruct a; try (intuition; fail).
      specialize (IHouts H3); inv IHouts.
      econstructor.
      + instantiate (1:= [RlblOuts mouts] :: trss); reflexivity.
      + simpl; rewrite H0; reflexivity.
      + constructor; auto.
        eapply STrsOuts; reflexivity.
  Qed.

  Lemma ssequential_atomicEx:
    forall atms,
      Forall (AtomicEx msgT_dec) atms ->
      SSequential msgT_dec (List.concat atms) (List.length atms).
  Proof.
    induction atms; simpl; intros.
    - apply SSeqIntro with (trss:= nil); auto.
    - inv H.
      specialize (IHatms H3); inv IHatms.
      econstructor.
      + instantiate (1:= a :: trss); rewrite H; reflexivity.
      + simpl; rewrite H0; reflexivity.
      + constructor; auto.
        red in H2; dest.
        eapply STrsAtomic; eauto.
  Qed.
  
  Lemma sequential_app:
    forall sys ll1 trss1 ll2 trss2,
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
    forall sys hst trss st,
      steps step_m sys (initsOf sys) hst st ->
      Sequential sys msg_dec hst trss ->
      Serializable sys hst st.
  Proof.
    intros; red; intros.
    eexists; split; eauto.
  Qed.

  Lemma stransactional_default:
    forall lbl, STransactional msgT_dec [lbl].
  Proof.
    destruct lbl; intros.
    - eapply STrsSlt.
    - eapply STrsIns; eauto.
    - eapply STrsAtomic.
      eapply atomic_singleton.
    - eapply STrsOuts; eauto.
  Qed.

  Lemma stransactional_cons_inv:
    forall lbl (hst: History MsgT),
      STransactional msgT_dec (lbl :: hst) ->
      hst = nil \/
      STransactional msgT_dec hst.
  Proof.
    intros.
    inv H; auto.
    inv H0; auto.
    right; econstructor; eauto.
  Qed.

  Lemma ssequential_default:
    forall hst, exists n, SSequential msgT_dec hst n.
  Proof.
    induction hst; simpl; intros; [repeat econstructor; eauto|].
    destruct IHhst as [n ?].
    destruct H; subst.
    exists (S (List.length trss)).
    econstructor.
    - instantiate (1:= [a] :: _); reflexivity.
    - reflexivity.
    - constructor; auto.
      apply stransactional_default.
  Qed.

  Lemma ssequential_app:
    forall ll1 n1 ll2 n2,
      SSequential msgT_dec ll1 n1 ->
      SSequential msgT_dec ll2 n2 ->
      SSequential msgT_dec (ll1 ++ ll2) (n1 + n2).
  Proof.
    intros.
    inv H; inv H0.
    econstructor.
    - rewrite <-concat_app; reflexivity.
    - apply eq_sym, app_length.
    - apply Forall_app; auto.
  Qed.

  Lemma atomicEx_stransactional:
    forall hst, AtomicEx msgT_dec hst -> STransactional msgT_dec hst.
  Proof.
    intros; inv H; dest.
    eapply STrsAtomic; eauto.
  Qed.

  Lemma atomicEx_stransactional_forall:
    forall trss, Forall (AtomicEx msgT_dec) trss ->
                 Forall (STransactional msgT_dec) trss.
  Proof.
    intros.
    eapply Forall_impl; [|eassumption].
    apply atomicEx_stransactional.
  Qed.
  
End MsgParam.

Lemma atomic_legal_eouts:
  forall (hst: MHistory) inits ins outs eouts,
    Atomic msg_dec inits ins hst outs eouts ->
    forall sys st1 st2,
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
    specialize (IHAtomic _ _ _ H6).
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

(* Lemma bequivalent_refl: *)
(*   forall sys {LabelT} `{HasLabel LabelT} (hst: list LabelT), *)
(*     BEquivalent sys hst hst. *)
(* Proof. *)
(*   congruence. *)
(* Qed. *)

(* Lemma bequivalent_sym: *)
(*   forall sys {LabelT} `{HasLabel LabelT} (hst1 hst2: list LabelT), *)
(*     BEquivalent sys hst1 hst2 -> *)
(*     BEquivalent sys hst2 hst1. *)
(* Proof. *)
(*   congruence. *)
(* Qed. *)

(* Lemma bequivalent_trans: *)
(*   forall sys {LabelT} `{HasLabel LabelT} (hst1 hst2 hst3: list LabelT), *)
(*     BEquivalent sys hst1 hst2 -> *)
(*     BEquivalent sys hst2 hst3 -> *)
(*     BEquivalent sys hst1 hst3. *)
(* Proof. *)
(*   congruence. *)
(* Qed. *)

(* Lemma bequivalent_app_1: *)
(*   forall sys {LabelT} `{HasLabel LabelT} (hst1 hst2 hst3: list LabelT), *)
(*     BEquivalent sys hst1 hst2 -> *)
(*     BEquivalent sys (hst3 ++ hst1) (hst3 ++ hst2). *)
(* Proof. *)
(*   intros. *)
(*   red; do 2 rewrite behaviorOf_app. *)
(*   f_equal; assumption. *)
(* Qed. *)

(* Lemma bequivalent_app_2: *)
(*   forall sys {LabelT} `{HasLabel LabelT} (hst1 hst2 hst3: list LabelT), *)
(*     BEquivalent sys hst1 hst2 -> *)
(*     BEquivalent sys (hst1 ++ hst3) (hst2 ++ hst3). *)
(* Proof. *)
(*   intros. *)
(*   red; do 2 rewrite behaviorOf_app. *)
(*   f_equal; assumption. *)
(* Qed. *)

(* Lemma ioEquivalent_refl: *)
(*   forall sys {LabelT} `{HasLabel LabelT} (hst: list LabelT), *)
(*     IOEquivalent sys hst hst. *)
(* Proof. *)
(*   congruence. *)
(* Qed. *)

(* Lemma ioEquivalent_sym: *)
(*   forall sys {LabelT} `{HasLabel LabelT} (hst1 hst2: list LabelT), *)
(*     IOEquivalent sys hst1 hst2 -> *)
(*     IOEquivalent sys hst2 hst1. *)
(* Proof. *)
(*   congruence. *)
(* Qed. *)

(* Lemma ioEquivalent_trans: *)
(*   forall sys {LabelT} `{HasLabel LabelT} (hst1 hst2 hst3: list LabelT), *)
(*     IOEquivalent sys hst1 hst2 -> *)
(*     IOEquivalent sys hst2 hst3 -> *)
(*     IOEquivalent sys hst1 hst3. *)
(* Proof. *)
(*   congruence. *)
(* Qed. *)

(* Lemma ioEquivalent_app_1: *)
(*   forall sys {LabelT} `{HasLabel LabelT} (hst1 hst2 hst3: list LabelT), *)
(*     IOEquivalent sys hst1 hst2 -> *)
(*     IOEquivalent sys (hst3 ++ hst1) (hst3 ++ hst2). *)
(* Proof. *)
(*   intros. *)
(*   red; unfold behaviorIO. *)
(*   do 2 (rewrite behaviorInsOf_app, behaviorOutsOf_app). *)
(*   inv H0; reflexivity. *)
(* Qed. *)

(* Lemma ioEquivalent_app_2: *)
(*   forall sys {LabelT} `{HasLabel LabelT} (hst1 hst2 hst3: list LabelT), *)
(*     IOEquivalent sys hst1 hst2 -> *)
(*     IOEquivalent sys (hst1 ++ hst3) (hst2 ++ hst3). *)
(* Proof. *)
(*   intros. *)
(*   red; unfold behaviorIO. *)
(*   do 2 (rewrite behaviorInsOf_app, behaviorOutsOf_app). *)
(*   inv H0; reflexivity. *)
(* Qed. *)

(* Theorem serializable_seqSteps_refinesIO: *)
(*   forall sys, *)
(*     SerializableSys sys -> *)
(*     steps step_m # seqStepsM |-- sys ≲ sys. *)
(* Proof. *)
(*   unfold SerializableSys, RefinesIO; intros. *)
(*   inv H0. *)
(*   specialize (H _ _ H1). *)
(*   unfold Serializable in H. *)
(*   destruct H as [sll [sst [? ?]]]. *)
(*   inv H0; unfold MLabel; rewrite H3, H4. *)
(*   econstructor; eauto. *)
(* Qed. *)

Lemma serializable_nil:
  forall sys, Serializable sys nil (initsOf sys).
Proof.
  intros; hnf; intros.
  exists nil; split.
  - constructor.
  - exists nil; constructor; auto.
Qed.

Lemma serializable_silent:
  forall sys ll st,
    Serializable sys ll st ->
    Serializable sys (RlblEmpty _ :: ll) st.
Proof.
  intros.
  hnf; hnf in H; intros; dest.
  destruct H; dest.
  eexists; split; eauto.
Qed.

Close Scope list.

