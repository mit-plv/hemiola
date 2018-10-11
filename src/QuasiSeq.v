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
       (exists rhst m, Reducible sys hst rhst /\
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
    - eapply reducible_serializable; eauto.
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

Definition ValidContinuous (sys: System) (hst1 hst2: MHistory) :=
  Continuous hst1 hst2 /\
  exists st1 st2 hst,
    steps step_m sys st1 (hst2 ++ hst ++ hst1) st2.

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
      ValidContinuous sys hst1 hst2 ->
      forall hsts,
        Forall (STransactional msg_dec) hsts ->
        Separated (hsts ++ [hst1]) ->
        Separated (hst2 :: hsts) ->
        exists rhst1 rhst2,
          Reducible sys (List.concat (hst2 :: hsts ++ [hst1]))
                    (List.concat (rhst2 ++ hst2 :: hst1 :: rhst1)) /\
          Forall (STransactional msg_dec) (rhst2 ++ rhst1) /\
          List.length hsts = List.length (rhst2 ++ rhst1).

  Lemma well_interleaved_reducible:
    forall (Hwi: WellInterleaved) trss st1 st2,
      steps step_m sys st1 (List.concat trss) st2 ->
      Forall (STransactional msg_dec) trss ->
      Interleaved trss ->
      exists (rhst : MHistory) (m : nat),
        Reducible sys (List.concat trss) rhst /\
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
    assert (ValidContinuous sys hst1 hst2) as Hvc.
    { split; auto.
      exists sti1, sti2, (List.concat hsts2).
      simpl in H5; rewrite concat_app in H5.
      simpl in H5; rewrite app_nil_r in H5.
      assumption.
    }
    pose proof (Hwi _ _ Hvc _ H6 H3 H4).
    destruct H7 as [rhst1 [rhst2 [? [? ?]]]].

    exists ((List.concat hsts3)
              ++ (List.concat (rhst2 ++ (hst2 ++ hst1) :: rhst1))
              ++ (List.concat hsts1)); eexists.
    split; [|split].
    - apply reducible_app_1.
      apply reducible_app_2.
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
      unfold MHistory, History, MLabel in *; rewrite H10.
      apply plus_lt_compat_l.
      rewrite app_length.
      rewrite <-Nat.add_assoc; simpl.
      repeat rewrite Nat.add_succ_r.
      rewrite Nat.add_assoc.
      auto.
  Qed.

  (* In order to give a stronger induction hypothesis between [WellInterleaved]
   * and [WellInterleavedPush]. *)
  Local Definition WellInterleavedPushHelper :=
    forall hst1 hst2,
      ValidContinuous sys hst1 hst2 ->
      forall hsts,
        Forall (STransactional msg_dec) hsts ->
        Separated (hsts ++ [hst1]) ->
        Separated (hst2 :: hsts) ->
        exists (lpush rpush: MHistory -> Prop) lhsts rhsts,
          Forall lpush lhsts /\ Forall rpush rhsts /\
          Reducible sys (List.concat (hsts ++ [hst1]))
                    (List.concat (rhsts ++ hst1 :: lhsts)) /\
          Reducible sys (hst2 ++ List.concat rhsts)
                    (List.concat rhsts ++ hst2) /\
          Forall (STransactional msg_dec) (rhsts ++ lhsts) /\
          List.length hsts = List.length (rhsts ++ lhsts).

  Lemma well_interleaved_push_helper_ok:
    forall (Hwip: WellInterleavedPushHelper), WellInterleaved.
  Proof.
    unfold WellInterleavedPushHelper, WellInterleaved; intros.
    specialize (Hwip _ _ H _ H0 H1 H2).
    destruct Hwip as [lpush [rpush [lhsts [rhsts ?]]]]; dest.
    exists lhsts, rhsts.
    split; auto.
    eapply reducible_trans.
    - simpl; apply reducible_app_1; eassumption.
    - repeat (simpl; try rewrite concat_app).
      repeat rewrite app_assoc.
      do 2 apply reducible_app_2.
      assumption.
  Qed.

  Definition WellInterleavedPush :=
    forall hst1 hst2,
      ValidContinuous sys hst1 hst2 ->
      exists (lpush rpush: MHistory -> Prop),
        rpush hst1 /\ lpush hst2 /\
        (forall lhst rhst,
            (* Do we need [~ Continuous] here? *)
            lpush lhst -> rpush rhst ->
            Reducible sys (lhst ++ rhst) (rhst ++ lhst)) /\
        forall hsts,
          Forall (STransactional msg_dec) hsts ->
          Separated (hsts ++ [hst1]) ->
          Separated (hst2 :: hsts) ->
          Forall (fun hst => lpush hst \/ rpush hst) hsts.
  
  Lemma well_interleaved_push_ok':
    forall (Hwip: WellInterleavedPush), WellInterleavedPushHelper.
  Proof.
    red; intros.
    specialize (Hwip _ _ H).
    destruct Hwip as [lpush [rpush ?]]; dest.
    exists lpush, rpush.

    specialize (H6 _ H0 H1 H2).
    generalize dependent hsts.

    induction hsts as [|hst hsts]; simpl; intros;
      [exists nil, nil; simpl; repeat rewrite app_nil_r; repeat split; auto|].

    inv H0; inv H6.
    apply separated_cons with (hsts2:= nil) in H1; dest; simpl in *; clear H1.
    apply separated_cons with (hsts2:= [hst2]) in H2; dest.
    inv H2; clear H15.

    specialize (IHhsts H11 H10 H6 H7).
    destruct IHhsts as [lhsts [rhsts ?]]; dest.
    destruct H8.

    - exists (hst :: lhsts), rhsts.
      repeat match goal with
             | [ |- _ /\ _] => split
             end; auto.
      + eapply reducible_trans;
          [apply reducible_app_1; eassumption|].
        repeat (simpl; try rewrite concat_app).
        eapply reducible_trans.
        * rewrite app_assoc.
          apply reducible_app_2.
          instantiate (1:= List.concat rhsts ++ hst).
          clear -H5 H8 H12.
          induction rhsts; simpl; [rewrite app_nil_r; apply reducible_refl|].
          inv H12.
          eapply reducible_trans.
          { rewrite app_assoc.
            apply reducible_app_2, H5; auto.
          }
          { do 2 rewrite <-app_assoc.
            apply reducible_app_1; auto.
          }
        * rewrite <-app_assoc.
          apply reducible_app_1.
          repeat rewrite app_assoc.
          apply reducible_app_2.
          apply H5; auto.
      + apply Forall_app_inv in H16; dest.
        apply Forall_app; auto.
      + rewrite app_length in H17.
        rewrite app_length; simpl.
        rewrite Nat.add_succ_r; congruence.

    - exists lhsts, (hst :: rhsts).
      repeat match goal with
             | [ |- _ /\ _] => split
             end; auto.
      + simpl; apply reducible_app_1; assumption.
      + specialize (H5 _ _ H4 H8).
        simpl; eapply reducible_trans.
        * rewrite app_assoc.
          apply reducible_app_2.
          eassumption.
        * do 2 rewrite <-app_assoc.
          apply reducible_app_1.
          assumption.
      + simpl; constructor; assumption.
      + simpl; congruence.
  Qed.

  Lemma well_interleaved_push_ok:
    forall (Hwip: WellInterleavedPush), WellInterleaved.
  Proof.
    intros.
    apply well_interleaved_push_helper_ok.
    apply well_interleaved_push_ok'; auto.
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
      right; eapply well_interleaved_reducible; eauto.
  Qed.

End WellInterleaved.

