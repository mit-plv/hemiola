Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT SemFacts.
Require Import Topology Serial SerialFacts Reduction.

Set Implicit Arguments.

Definition Prec := MState -> Prop.
Definition Trs := MState -> MState.

Definition DenotationalL (sys: System) (prec: Prec) (trs: Trs) (hst: MHistory) :=
  forall st1,
    prec st1 ->
    steps step_m sys st1 hst (trs st1).

Definition DenotationalR (sys: System) (prec: Prec) (trs: Trs) (hst: MHistory) :=
  forall st1 st2,
    steps step_m sys st1 hst st2 ->
    prec st1 /\ st2 = trs st1.

Definition Denotational (sys: System) (prec: Prec) (trs: Trs) (hst: MHistory) :=
  DenotationalL sys prec trs hst /\
  DenotationalR sys prec trs hst.

Definition NonconflictingD (p1 p2: Prec) (f1 f2: Trs) :=
  (forall o, p2 (f1 o) -> p2 o) /\
  (forall o, p1 o -> p1 (f2 o)) /\
  (forall o, f2 (f1 o) = f1 (f2 o)).

Lemma silent_denotational:
  forall sys, Denotational sys (fun _ => True) id [RlblEmpty _].
Proof.
  intros.
  hnf; split; hnf; intros.
  - repeat econstructor.
  - inv H; inv H3; inv H5; auto.
Qed.

Lemma ins_denotational:
  forall sys eins,
    eins <> nil ->
    ValidMsgsExtIn sys eins ->
    Denotational sys (fun _ => True)
                 (fun st => {| bst_oss := bst_oss st;
                               bst_orqs := bst_orqs st;
                               bst_msgs := enqMsgs eins (bst_msgs st) |})
                 [RlblIns eins].
Proof.
  intros.
  hnf; split; hnf; intros.
  - econstructor.
    + econstructor.
    + econstructor; eauto.
      destruct st1; reflexivity.
  - inv H1; inv H5; inv H7; auto.
Qed.

Lemma outs_denotational:
  forall sys eouts,
    eouts <> nil ->
    ValidMsgsExtOut sys eouts ->
    Denotational sys (fun st => Forall (FirstMPI (bst_msgs st)) eouts)
                 (fun st => {| bst_oss := bst_oss st;
                               bst_orqs := bst_orqs st;
                               bst_msgs := deqMsgs (idsOf eouts) (bst_msgs st) |})
                 [RlblOuts eouts].
Proof.
  intros.
  hnf; split; hnf; intros.
  - econstructor.
    + econstructor.
    + econstructor; eauto.
      destruct st1; reflexivity.
  - inv H1; inv H5; inv H7; auto.
Qed.

Inductive DenoteIntHst: Prec -> Trs -> MHistory -> Prop :=
| DenoteNil: DenoteIntHst (fun _ => True) id nil
| DenoteCons:
    forall p f hst,
      DenoteIntHst p f hst ->
      forall rule ins outs,
        DenoteIntHst
          (fun st =>
             p st /\
             let oss := bst_oss (f st) in
             let orqs := bst_orqs (f st) in
             let msgs := bst_msgs (f st) in
             Forall (FirstMPI msgs) ins /\
             exists ost orq,
               oss@[rule_oidx rule] = Some ost /\
               orqs@[rule_oidx rule] = Some orq /\
               rule_precond rule ost orq ins /\
               snd (rule_trs rule ost orq ins) = outs
          )
          (fun st =>
             let oss := bst_oss (f st) in
             let orqs := bst_orqs (f st) in
             let msgs := bst_msgs (f st) in
             oss@[rule_oidx rule] >>=[st]
                (fun ost =>
                   orqs@[rule_oidx rule] >>=[st]
                       (fun orq =>
                          match rule_trs rule ost orq ins with
                          | (nost, norq, _) =>
                            {| bst_oss := oss +[rule_oidx rule <- nost];
                               bst_orqs := orqs +[rule_oidx rule <- norq];
                               bst_msgs := enqMsgs outs (deqMsgs (idsOf ins) msgs)
                            |}
                          end)))
          (RlblInt rule ins outs :: hst).

Lemma denoteIntHst_prec_trs_exist:
  forall hst,
    InternalHistory hst ->
    exists p f, DenoteIntHst p f hst.
Proof.
  induction hst; simpl; intros.
  - do 2 eexists; constructor.
  - inv H.
    specialize (IHhst H3).
    destruct IHhst as [pp [pf ?]].
    destruct a as [| |rule ins outs|]; try (elim H2; fail).
    do 2 eexists.
    econstructor; eauto.
Qed.

Lemma denoteIntHst_denotationalL:
  forall sys p f hst,
    WfHistory sys hst ->
    DenoteIntHst p f hst ->
    DenotationalL sys p f hst.
Proof.
  induction 2; simpl; intros; [constructor|].
  inv H; econstructor; [destruct H; eapply IHDenoteIntHst; eauto|].
  dest.
  remember (rule_trs rule x x0 ins) as nst.
  destruct nst as [[noss norqs] nmsgs].
  apply eq_sym in Heqnst.
  simpl in H7; subst.
  red in H3; dest.
  econstructor; try reflexivity; try eassumption; simpl.
  - destruct (f st1); reflexivity.
  - rewrite H2, H5; simpl.
    rewrite Heqnst; reflexivity.
Qed.

Lemma denoteIntHst_denotationalR:
  forall sys p f hst,
    DenoteIntHst p f hst ->
    DenotationalR sys p f hst.
Proof.
  induction 1; simpl; intros;
    [red; intros; inv H; auto|].

  red; intros; inv H0.
  specialize (IHDenoteIntHst _ _ H4); dest; subst.
  inv H6; rewrite H21; simpl.
  repeat split; auto.
  - do 2 eexists; repeat split; try eassumption.
    rewrite H16; reflexivity.
  - rewrite H8, H9; simpl.
    rewrite H16; reflexivity.
Qed.

Lemma denoteIntHst_denotational:
  forall sys p f hst,
    WfHistory sys hst ->
    DenoteIntHst p f hst ->
    Denotational sys p f hst.
Proof.
  intros; split.
  - apply denoteIntHst_denotationalL; auto.
  - apply denoteIntHst_denotationalR; auto.
Qed.

Lemma atomic_denotational:
  forall sys inits ins hst outs eouts,
    WfHistory sys hst ->
    Atomic msg_dec inits ins hst outs eouts ->
    exists p f,
      Denotational sys p f hst /\
      DenoteIntHst p f hst.
Proof.
  intros.
  apply atomic_internal_history in H0.
  apply denoteIntHst_prec_trs_exist in H0.
  destruct H0 as [p [f ?]].
  pose proof (denoteIntHst_denotational H H0).
  eauto.
Qed.

Definition trsTypeOf (hst: MHistory) :=
  match hst with
  | nil => TSlt
  | lbl :: _ =>
    match lbl with
    | RlblEmpty _ => TSlt
    | RlblIns _ => TIns
    | RlblOuts _ => TOuts
    | RlblInt _ _ _ => TInt
    end
  end.

Definition DiscontinuousTrsType (tty1 tty2: TrsType) :=
  match tty1, tty2 with
  | TSlt, _ => True
  | _, TSlt => True
  | TInt, _ => True
  | _, TInt => True
  | _, _ => False
  end.

Definition NonconflictingI (hst1 hst2: MHistory) :=
  forall eins1 inits2 ins2 outs2 eouts2,
    hst1 = [RlblIns eins1] ->
    Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
    DisjList eins1 ins2 /\ DisjList (idsOf eins1) (idsOf outs2).

Definition NonconflictingO (hst1 hst2: MHistory) :=
  forall inits1 ins1 outs1 eouts1 eouts2,
    Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
    hst2 = [RlblOuts eouts2] ->
    DisjList (idsOf eouts2) (idsOf ins1) /\ DisjList eouts2 outs1.

Definition NonconflictingA (sys: System) (hst1 hst2: MHistory) :=
  forall inits1 ins1 outs1 eouts1 inits2 ins2 outs2 eouts2,
    Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 ->
    Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 ->
    exists p1 p2 f1 f2,
      Denotational sys p1 f1 hst1 /\
      Denotational sys p2 f2 hst2 /\
      NonconflictingD p1 p2 f1 f2.

Definition Nonconflicting (sys: System) (hst1 hst2: MHistory) :=
  STransactional msg_dec hst1 /\
  STransactional msg_dec hst2 /\
  DiscontinuousTrsType (trsTypeOf hst1) (trsTypeOf hst2) /\
  NonconflictingI hst1 hst2 /\
  NonconflictingO hst1 hst2 /\
  NonconflictingA sys hst1 hst2.

Definition BCommutable (sys: System) (hst1 hst2: MHistory) :=
  behaviorOf sys hst2 ++ behaviorOf sys hst1 =
  behaviorOf sys hst1 ++ behaviorOf sys hst2.

Lemma nonconflictingD_reduced:
  forall sys hst1 hst2 p1 p2 f1 f2,
    BCommutable sys hst1 hst2 ->
    Denotational sys p1 f1 hst1 ->
    Denotational sys p2 f2 hst2 ->
    NonconflictingD p1 p2 f1 f2 ->
    Reduced sys (hst2 ++ hst1) (hst1 ++ hst2).
Proof.
  intros; red; intros.
  split.
  - eapply steps_split in H3; [|reflexivity].
    destruct H3 as [sti [? ?]].
    red in H0, H1; dest.
    specialize (H6 _ _ H3); specialize (H5 _ _ H4); dest; subst.
    red in H2; dest.
    specialize (H2 _ H5).
    specialize (H1 _ H2).
    specialize (H7 _ H6).
    specialize (H0 _ H7).
    rewrite H8.
    eapply steps_append; eauto.
  - red; do 2 rewrite behaviorOf_app; assumption.
Qed.

Lemma nonconflicting_reduced:
  forall sys hst1 hst2,
    Nonconflicting sys hst1 hst2 ->
    Reduced sys (hst2 ++ hst1) (hst1 ++ hst2).
Proof.
  unfold Nonconflicting; intros; dest.
  inv H.
  - apply silent_reduced_2.
  - inv H0; try (elim H1; fail).
    + apply silent_reduced_1.
    + specialize (H2 _ _ _ _ _ eq_refl H); dest.
      eapply msg_ins_reduced_2; eauto.
  - inv H0; try (elim H1; fail).
    + apply silent_reduced_1.
    + apply msg_outs_reduced_1.
      eapply atomic_internal_history; eauto.
  - inv H0.
    + apply silent_reduced_1.
    + apply msg_ins_reduced_1.
      eapply atomic_internal_history; eauto.
    + red in H3.
      specialize (H3 _ _ _ _ _ H5 eq_refl); dest.
      eapply msg_outs_reduced_2; eauto.
    + red in H4.
      specialize (H4 _ _ _ _ _ _ _ _ H5 H).
      destruct H4 as [p1 [p2 [f1 [f2 [? [? ?]]]]]].
      eapply nonconflictingD_reduced; eauto.
      apply atomic_internal_history in H.
      apply atomic_internal_history in H5.
      red.
      do 2 (rewrite internal_history_behavior_nil by assumption).
      reflexivity.
Qed.

