Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap.
Require Import Syntax Semantics SemFacts StepT Serial Invariant.

Require Import Omega.
Require Import Program.Equality.

Set Implicit Arguments.

Lemma atomic_emptyILabel_not_in:
  forall sys ts rq hst mouts,
    Atomic sys ts rq hst mouts ->
    ~ In (emptyRLabel _) hst.
Proof.
  induction 1; simpl; intros.
  - intro Hx; destruct Hx; [discriminate|auto].
  - intro Hx; destruct Hx; auto.
    inv H2; elim H0; reflexivity.
Qed.

Lemma atomic_iLblIn_not_in:
  forall sys ts rq hst mouts,
    Atomic sys ts rq hst mouts ->
    forall msg,
      ~ In (RlblIns [msg]) hst.
Proof.
  induction 1; simpl; intros; [auto|];
    try (intro Hx; destruct Hx;
         [discriminate|firstorder]).
Qed.

Lemma atomic_preserved:
  forall impl1 ts rq hst mouts,
    Atomic impl1 ts rq hst mouts ->
    forall impl2,
      merqsOf impl1 = merqsOf impl2 ->
      Atomic impl2 ts rq hst mouts.
Proof.
  induction 1; simpl; intros.
  - econstructor; eauto.
    simpl in *.
    rewrite H1 in H; assumption.
  - econstructor; eauto.
Qed.

Theorem atomic_tinfo:
  forall sys ts rq hst mouts,
    Atomic sys ts rq hst mouts ->
    forall st1 st2,
      steps step_t sys st1 hst st2 ->
      Forall (fun lbl => match lbl with
                         | RlblInt _ ins outs =>
                           Forall (fun idt =>
                                     match tmsg_info (valOf idt) with
                                     | Some hti => hti = buildTInfo ts [rq]
                                     | None => liftI tmsg_msg idt = rq
                                     end) ins /\
                           Forall (fun idt =>
                                     tmsg_info (valOf idt) =
                                     Some (buildTInfo ts [rq])) outs
                         | _ => False
                         end) hst /\
      ForallMP (fun midx tmsg =>
                  tmsg_info tmsg = Some (buildTInfo ts [rq])) mouts.
Proof.
  induction 1; simpl; intros.

  - split.
    + constructor; auto.
      split; auto.
      constructor; cbn; auto.
      destruct rq as [midx rq]; reflexivity.
    + inv H1; inv H5; inv H7.
      cbn in *.
      apply ForallMP_enqMsgs.
      * apply ForallMP_emptyMP.
      * clear -H0.
        induction outs; simpl; [constructor|].
        inv H0.
        constructor; auto.

  - inv H2.
    specialize (IHAtomic _ _ H6); destruct IHAtomic.
    split.
    + constructor; auto.
      assert (Forall (fun idt =>
                        tmsg_info (valOf idt) = Some (buildTInfo ts [rq])) msgs).
      { eapply ForallMP_Forall_InMP in H3; eauto. }
      
      split.
      * clear -H4; eapply Forall_impl; eauto.
        simpl; intros.
        rewrite H; reflexivity.
      * inv H8.
        assert (Forall (fun idt =>
                          tmsg_info (valOf idt) = Some (buildTInfo ts [rq])) msgs).
        { clear -H4; eapply Forall_impl; eauto.
          simpl; intros.
          destruct H; auto.
        }

        rewrite getTMsgsTInfo_Forall_Some with (ti:= buildTInfo ts [rq]).
        { clear; induction outs; constructor; auto. }
        { destruct msgs; [auto|discriminate]. }
        { clear -H5; induction msgs; [constructor|].
          inv H5; constructor; auto.
        }
        
    + apply ForallMP_enqMsgs.
      * apply ForallMP_deqMsgs; auto.
      * apply ForallMP_Forall_InMP with (ims:= msgs) in H3; auto.
        inv H8.
        destruct msgs as [|msg msgs]; [elim H0; reflexivity|].
        inv H3; cbn; unfold valOf in H7; rewrite H7.
        clear; induction outs; [constructor|].
        constructor; auto.
Qed.

Corollary atomic_hst_tinfo:
  forall sys ts rq hst mouts,
    Atomic sys ts rq hst mouts ->
    forall st1 st2,
      steps step_t sys st1 hst st2 ->
      Forall (fun lbl => match lbl with
                         | RlblInt _ ins outs =>
                           Forall (fun idt =>
                                     match tmsg_info (valOf idt) with
                                     | Some hti => hti = buildTInfo ts [rq]
                                     | None => liftI tmsg_msg idt = rq
                                     end) ins /\
                           Forall (fun idt =>
                                     tmsg_info (valOf idt) =
                                     Some (buildTInfo ts [rq])) outs
                         | _ => False
                         end) hst.
Proof.
  intros.
  eapply atomic_tinfo in H; eauto.
  destruct H; auto.
Qed.

Corollary atomic_mouts_tinfo:
  forall sys ts rq hst mouts,
    Atomic sys ts rq hst mouts ->
    forall st1 st2,
      steps step_t sys st1 hst st2 ->
      ForallMP (fun midx tmsg =>
                  tmsg_info tmsg = Some (buildTInfo ts [rq])) mouts.
Proof.
  intros.
  eapply atomic_tinfo in H; eauto.
  destruct H; auto.
Qed.

Theorem serializable_seqSteps_refines:
  forall sys,
    SerializableSys sys ->
    steps step_t # seqSteps |-- sys ⊑ sys.
Proof.
  unfold SerializableSys, Refines; intros.
  inv H0; rename ll0 into ill.
  specialize (H _ _ H1).
  unfold Serializable in H.
  destruct H as [sll [sst [? ?]]].
  rewrite H0.
  econstructor; eauto.
Qed.

Lemma sequential_nil:
  forall sys, Sequential sys nil.
Proof.
  intros; hnf; intros.
  exists nil.
  split.
  - constructor.
  - reflexivity.
Qed.

Lemma sequential_silent:
  forall sys ll,
    Sequential sys ll ->
    Sequential sys (emptyRLabel _ :: ll).
Proof.
  intros.
  hnf; hnf in H; dest.
  eexists ([emptyRLabel _] :: _); split.
  - constructor; [|eassumption].
    constructor.
  - subst; reflexivity.
Qed.

Lemma sequential_msg_ins:
  forall sys ll eins,
    Sequential sys ll ->
    Sequential sys (RlblIns eins :: ll).
Proof.
  intros.
  hnf; hnf in H; dest.
  eexists ([RlblIns eins] :: _); split.
  - constructor; [|eassumption].
    eapply TrsIns; reflexivity.
  - subst; reflexivity.
Qed.

Lemma sequential_msg_outs:
  forall sys ll eouts,
    Sequential sys ll ->
    Sequential sys (RlblOuts eouts :: ll).
Proof.
  intros.
  hnf; hnf in H; dest.
  eexists ([RlblOuts eouts] :: _); split.
  - constructor; [|eassumption].
    eapply TrsOuts; reflexivity.
  - subst; reflexivity.
Qed.

Lemma serializable_nil:
  forall sys, Serializable sys nil.
Proof.
  intros; hnf; intros.
  exists nil; eexists.
  split.
  - split.
    + constructor.
    + apply sequential_nil.
  - reflexivity.
Qed.

Lemma serializable_silent:
  forall sys ll,
    Serializable sys ll ->
    Serializable sys (emptyRLabel _ :: ll).
Proof.
  intros.
  hnf; hnf in H; intros; dest.
  do 2 eexists; split.
  - destruct H; split.
    + eapply StepsCons.
      * eassumption.
      * eapply StSlt.
    + apply sequential_silent; auto.
  - assumption.
Qed.

Lemma serializable_msg_ins:
  forall sys ll eins,
    Serializable sys ll ->
    eins <> nil ->
    ValidMsgsExtIn sys eins ->
    Serializable sys (RlblIns (imap toTMsgU eins) :: ll).
Proof.
  intros.
  hnf; hnf in H; intros; dest.
  destruct x0 as [oss orqs msgs trss ts].
  exists (RlblIns (imap toTMsgU eins) :: x); eexists; split.
  - destruct H; split.
    + econstructor.
      * eassumption.
      * econstructor; eauto.
    + apply sequential_msg_ins; auto.
  - hnf; cbn; rewrite H2; reflexivity.
Qed.

Lemma serializable_steps_no_rules:
  forall sys,
    sys_rules sys = nil ->
    forall st1,
      st1 = initsOf sys ->
      forall ll st2,
        steps step_t sys st1 ll st2 ->
        Serializable sys ll.
Proof.
  induction 3; simpl; intros.
  - apply serializable_nil.
  - specialize (IHsteps H0); subst.
    inv H2.
    + apply serializable_silent; auto.
    + apply serializable_msg_ins; auto.
    + exfalso.
      eapply behavior_no_rules_NoExtOuts in H1; eauto.
      red in H1; simpl in H1.
      destruct eouts as [|eout eouts]; auto.
      inv H3.
      destruct H4.
      simpl in H2; apply SubList_cons_inv in H2; dest.
      apply FirstMP_InMP in H6.
      eapply ForallMP_InMP in H1; eauto.
    + exfalso.
      rewrite H in H10.
      elim H10.
Qed.
                           
Lemma serializable_no_rules:
  forall sys,
    sys_rules sys = nil ->
    SerializableSys sys.
Proof.
  intros; hnf; intros.
  eapply serializable_steps_no_rules; eauto.
Qed.

