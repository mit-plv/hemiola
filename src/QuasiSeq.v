Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT SemFacts.
Require Import Serial SerialFacts Reduction.

Require Import Omega Wf.

Set Implicit Arguments.

(*! Quasi-sequential histories *)

Section QuasiSeq.
  Variables (sys: System)
            (quasiSeq: forall (sys: System) (hst: MHistory) (n: nat), Prop).

  Definition QuasiSeqOkInit :=
    forall hst st,
      steps step_m sys (initsOf sys) hst st ->
      exists n, quasiSeq sys hst n.

  Definition QuasiSeqOkStep :=
    forall hst st n,
      steps step_m sys (initsOf sys) hst st ->
      quasiSeq sys hst n ->
      ((exists trss, Sequential sys msg_dec hst trss) \/
       (exists rhst m, Reduced sys hst rhst /\
                       quasiSeq sys rhst m /\ m < n)).

  Lemma quasiSeq_implies_serializableSys:
    QuasiSeqOkStep ->
    forall n hst st,
      steps step_m sys (initsOf sys) hst st ->
      quasiSeq sys hst n ->
      Serializable sys hst.
  Proof.
    induction n as [n IHn] using (well_founded_induction lt_wf).
    intros.
    specialize (H _ _ _ H0 H1); destruct H; dest.
    - eapply sequential_serializable; eauto.
    - eapply reduced_serializable; eauto.
      eapply IHn; eauto.
      eapply H; eauto.
  Qed.

  Lemma quasiSeqOk_implies_serializableSys:
    QuasiSeqOkInit -> QuasiSeqOkStep -> SerializableSys sys.
  Proof.
    intros; red; intros.
    specialize (H _ _ H1); destruct H as [n ?].
    eapply quasiSeq_implies_serializableSys; eauto.
  Qed.

End QuasiSeq.

(*! Semi-sequential (as quasi-sequential) histories *)

(* The number of [STransactional] segments is the decreasing factor when
 * defining [SSequential] as a predicate for quasi-sequential histories.
 *
 * In a bird's eye view, how do we know that number is decreasing?
 * 0) For a given legal history [hst], always [exists n, SSequential hst n]
 * 1) When a history is semi-sequential, 
 *    it's either [Sequential] or [Interleaved]
 * 2) If a history is [Interleaved], then it's [MinInterleaved].
 * 3) Let [hst1] and [hst2] be minimally-interleaving sequences in [hst].
 *    [WellInterleaved] says that [hst1] and [hst2] can be merged by a number
 *    of reductions.
 * 4) [WellInterleaved] directly implies [Serializable].
 *)

Definition Continuous (hst1 hst2: MHistory) :=
  exists inits1 ins1 outs1 eouts1 inits2 ins2 outs2 eouts2,
    Atomic msg_dec inits1 ins1 hst1 outs1 eouts1 /\
    Atomic msg_dec inits2 ins2 hst2 outs2 eouts2 /\
    inits2 <> nil /\
    SubList inits2 eouts1.

Definition Separated (hsts: list MHistory) :=
  forall hst1 hst2 hsts1 hsts2 hsts3,
    hsts = hsts3 ++ hst2 :: hsts2 ++ hst1 :: hsts1 ->
    ~ Continuous hst1 hst2.

Definition Interleaved (hsts: list MHistory) :=
  exists hst1 hst2 hsts1 hsts2 hsts3,
    hsts = hsts3 ++ hst2 :: hsts2 ++ hst1 :: hsts1 /\
    Continuous hst1 hst2.

Definition MinInterleaved (hsts: list MHistory) :=
  exists hst1 hst2 hsts1 hsts2 hsts3,
    hsts = hsts3 ++ hst2 :: hsts2 ++ hst1 :: hsts1 /\
    Continuous hst1 hst2 /\
    Separated (hsts2 ++ [hst1]) /\
    Separated (hst2 :: hsts2).

Lemma interleaved_min:
  forall hsts, Interleaved hsts -> MinInterleaved hsts.
Proof.
Admitted.

Lemma separated_cons:
  forall (hsts1 hsts2: list MHistory) hst,
    Separated (hsts2 ++ hst :: hsts1) ->
    Forall (fun phst => ~ Continuous phst hst) hsts1 /\
    Forall (fun nhst => ~ Continuous hst nhst) hsts2 /\
    Separated (hsts2 ++ hsts1).
Proof.
Admitted.

Lemma continuous_atomic_concat:
  forall (hst1 hst2: MHistory),
    Continuous hst1 hst2 ->
    exists inits ins outs eouts,
      Atomic msg_dec inits ins (hst2 ++ hst1) outs eouts.
Proof.
  unfold Continuous; intros; dest.
  pose proof (atomic_app H H1 H0 H2); dest.
  eauto.
Qed.

Lemma stransactional_sequential_or_interleaved:
  forall sys trss st,
    steps step_m sys (initsOf sys) (List.concat trss) st ->
    Forall (STransactional msg_dec) trss ->
    Sequential sys msg_dec (List.concat trss) trss \/
    Interleaved trss.
Proof.
  induction trss as [|trs trss]; simpl; intros;
    [left; constructor; auto|].

  eapply steps_split in H; [|reflexivity].
  destruct H as [sti [? ?]].
  inv H0.
  specialize (IHtrss _ H H5); destruct IHtrss.

  - (* TODO: need to prove that whenever a semi-transaction
     * [STransactional ins trs outs] is added to a history ([List.concat trss]),
     * [ins] is either a new semi-transaction or a continuation from one of 
     * previous semi-transactions.
     *
     * This is not true when [ins] takes a part from [trs1] and the other part
     * from [trs2], where [trs1 <> trs2] and [trs1 ∈ trss /\ trs2 ∈ trss].
     * Thus we need a static condition to ensure each rule in the system takes
     * incoming messages for a single transaction.
     *)
    admit.
  - right.
    clear -H0.
    destruct H0 as [hst1 [hst2 [hsts1 [hsts2 [hsts3 [? ?]]]]]]; subst.
    exists hst1, hst2, hsts1, hsts2, (trs :: hsts3).
    split; auto.
Admitted.

Section WellInterleaved.
  Variable (sys: System).

  Definition WellInterleaved :=
    forall hst1 hst2,
      Continuous hst1 hst2 ->
      forall hsts,
        Forall (STransactional msg_dec) hsts ->
        Separated (hsts ++ [hst1]) ->
        Separated (hst2 :: hsts) ->
        exists rhst1 rhst2,
          Reduced sys (List.concat (hst2 :: hsts ++ [hst1]))
                  (List.concat (rhst2 ++ hst2 :: hst1 :: rhst1)) /\
          Forall (STransactional msg_dec) (rhst2 ++ rhst1) /\
          List.length hsts = List.length (rhst2 ++ rhst1).

  Lemma well_interleaved_reduced:
    forall (Hwi: WellInterleaved) trss st1 st2,
      steps step_m sys st1 (List.concat trss) st2 ->
      Forall (STransactional msg_dec) trss ->
      Interleaved trss ->
      exists (rhst : MHistory) (m : nat),
        Reduced sys (List.concat trss) rhst /\
        SSequential msg_dec rhst m /\
        m < Datatypes.length trss.
  Proof.
    intros.
    apply interleaved_min in H1.
    destruct H1 as [hst1 [hst2 [hsts1 [hsts2 [hsts3 [? [? [? ?]]]]]]]]; subst.
    match goal with
    | [H: steps step_m _ _ ?hst _ |- _] =>
      replace hst with ((List.concat hsts3)
                          ++ (List.concat (hst2 :: hsts2 ++ [hst1]))
                          ++ (List.concat hsts1)) in *;
        [|simpl; repeat rewrite <-app_assoc;
          repeat rewrite concat_app; simpl;
          rewrite <-app_assoc, app_nil_r;
          repeat rewrite concat_app; simpl;
          reflexivity]
    end.
    eapply steps_split in H; [|reflexivity]; destruct H as [sti2 [? ?]].
    eapply steps_split in H; [|reflexivity]; destruct H as [sti1 [? ?]].
    apply Forall_app_inv in H0; dest.
    inv H6; apply Forall_app_inv in H10; dest; inv H7.
    pose proof (Hwi _ _ H2 _ H6 H3 H4).
    destruct H7 as [rhst1 [rhst2 [? [? ?]]]].

    exists ((List.concat hsts3)
              ++ (List.concat (rhst2 ++ (hst2 ++ hst1) :: rhst1))
              ++ (List.concat hsts1)); eexists.
    split; [|split].
    - apply reduced_app_1.
      apply reduced_app_2.
      replace (List.concat (rhst2 ++ (hst2 ++ hst1) :: rhst1))
        with (List.concat (rhst2 ++ hst2 :: hst1 :: rhst1)); [assumption|].
      repeat (rewrite concat_app; simpl).
      rewrite <-app_assoc; reflexivity.
    - econstructor.
      + repeat rewrite <-concat_app; reflexivity.
      + reflexivity.
      + apply Forall_app_inv in H8; dest.
        repeat (apply Forall_app; auto).
        constructor; auto.
        eapply continuous_atomic_concat in H2; eauto.
        destruct H2 as [inits [ins [outs [eouts ?]]]].
        eapply STrsAtomic; eauto.
    - repeat (simpl; try rewrite app_length).
      unfold MHistory; rewrite H10.
      apply plus_lt_compat_l.
      rewrite app_length.
      rewrite <-Nat.add_assoc; simpl.
      repeat rewrite Nat.add_succ_r.
      rewrite Nat.add_assoc.
      auto.
  Qed.

  Definition WellInterleavedInd :=
    forall hst1 hst2,
      Continuous hst1 hst2 ->
      forall hst,
        STransactional msg_dec hst ->
        forall hsts,
          Forall (STransactional msg_dec) hsts ->
          Forall (fun phst => ~ Continuous phst hst) (hsts ++ [hst1]) ->
          ~ Continuous hst hst2 ->
          Reduced sys (hst2 ++ hst ++ List.concat hsts ++ hst1)
                  (hst2 ++ List.concat hsts ++ hst1 ++ hst) \/
          Reduced sys (hst2 ++ hst ++ List.concat hsts ++ hst1)
                  (hst ++ hst2 ++ List.concat hsts ++ hst1).

  Lemma well_interleaved_ind_ok:
    forall (Hwii: WellInterleavedInd), WellInterleaved.
  Proof.
    red; induction hsts as [|hst hsts]; simpl; intros;
      [exists nil, nil; simpl; split; auto; apply reduced_refl|].

    inv H0.

    apply separated_cons with (hsts2:= nil) in H1; dest; simpl in *; clear H1.
    apply separated_cons with (hsts2:= [hst2]) in H2; dest.
    inv H2; clear H10.
    
    specialize (IHhsts H6 H3 H4).
    destruct IHhsts as [rhst1 [rhst2 ?]]; dest.

    eapply Hwii in H6; eauto.
    specialize (H6 H0 H9).
    destruct H6.
    - exists (rhst1 ++ [hst]), rhst2.
      split; [|split].
      + repeat (simpl; try rewrite concat_app; try rewrite app_nil_r).
        repeat (simpl in H2; try rewrite concat_app in H2; try rewrite app_nil_r in H2).
        eapply reduced_trans; [eassumption|].
        repeat rewrite app_assoc.
        apply reduced_app_2.
        repeat rewrite <-app_assoc.
        assumption.
      + apply Forall_app_inv in H7; dest.
        repeat apply Forall_app; eauto.
      + repeat rewrite app_length.
        rewrite app_length in H8.
        rewrite Nat.add_assoc, <-H8.
        simpl; omega.
    - exists rhst1, (hst :: rhst2).
      split; [|split].
      + repeat (simpl; try rewrite concat_app; try rewrite app_nil_r).
        repeat (simpl in H2; try rewrite concat_app in H2; try rewrite app_nil_r in H2).
        eapply reduced_trans; [eassumption|].
        apply reduced_app_1.
        assumption.
      + apply Forall_app_inv in H7; dest.
        repeat apply Forall_app; eauto.
      + simpl; rewrite app_length.
        rewrite app_length in H8.
        rewrite <-H8.
        auto.
  Qed.

  Lemma well_interleaved_serializable:
    WellInterleaved -> SerializableSys sys.
  Proof.
    intros.
    apply quasiSeqOk_implies_serializableSys
      with (quasiSeq := fun _ hst n => SSequential msg_dec hst n).
    - red; intros.
      apply ssequential_default.
    - red; intros.
      inv H1.
      pose proof (stransactional_sequential_or_interleaved H0 H4).
      destruct H1; eauto.
      right; eapply well_interleaved_reduced; eauto.
  Qed.

End WellInterleaved.

