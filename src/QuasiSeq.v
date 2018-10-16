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
    forall hst n st,
      steps step_m sys (initsOf sys) hst st ->
      quasiSeq sys hst n ->
      ((exists trss, Sequential sys msg_dec hst trss) \/
       (exists rhst m,
           steps step_m sys (initsOf sys) rhst st /\
           BEquivalent sys hst rhst /\
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
    specialize (H _ _ _ H0 H1); destruct H.
    - dest; eapply sequential_serializable; eauto.
    - destruct H as [rhst [m ?]]; dest.
      specialize (IHn _ H4 _ _ H H3).
      eapply reducible_serializable with (hto:= rhst); eauto.
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

Lemma list_picker:
  forall (A: Type) (P: list A -> Prop) (f: P nil)
         (Q0: A -> Prop) (Q1: A -> Prop)
         (f0: forall l, Forall Q0 l -> P l)
         (f1: forall a l0 l1,
             Forall Q0 l0 -> Q1 a ->
             P (l0 ++ l1) -> P (l0 ++ a :: l1)),
  forall l, Forall (fun a => Q0 a \/ Q1 a) l ->
            (Forall Q0 l \/
             exists a l0 l1, l = l0 ++ a :: l1 /\ Forall Q0 l0 /\ Q1 a).
Proof.
  induction l; simpl; intros; auto.
  inv H; destruct H2.
  - specialize (IHl H3).
    destruct IHl.
    + left; constructor; auto.
    + destruct H0 as [a0 [l0 [l1 ?]]]; dest; subst.
      right; exists a0, (a :: l0), l1.
      repeat split; auto.
  - right; exists a, nil, l; repeat split; auto.
Qed.

Lemma list_ind_pick:
  forall (A: Type) (P: list A -> Prop) (f: P nil)
         (Q0: A -> Prop) (Q1: A -> Prop)
         (f0: forall l, Forall Q0 l -> P l)
         (f1: forall a l0 l1,
             Forall Q0 l0 -> Q1 a ->
             P (l0 ++ l1) -> P (l0 ++ a :: l1)),
  forall l, Forall (fun a => Q0 a \/ Q1 a) l -> P l.
Proof.
  intros.
  remember (List.length l) as n.
  generalize dependent l.

  induction n; intros;
    [apply eq_sym, length_zero_iff_nil in Heqn; subst; auto|].

  pose proof H.
  eapply list_picker in H0; eauto.
  destruct H0; auto.
  destruct H0 as [a0 [l0 [l1 ?]]]; dest; subst.
  eapply f1; eauto.
  eapply IHn.
  - apply Forall_app_inv in H; dest; inv H0.
    apply Forall_app; auto.
  - rewrite app_length in Heqn; simpl in Heqn.
    rewrite app_length; omega.
Qed.

Section WellInterleaved.
  Variable (sys: System).

  Definition WellInterleaved :=
    forall st1 st2 hst1 hst2 hsts,
      steps step_m sys st1 (List.concat (hst2 :: hsts ++ [hst1])) st2 ->
      Continuous hst1 hst2 ->
      Forall (STransactional msg_dec) hsts ->
      Separated (hsts ++ [hst1]) ->
      Separated (hst2 :: hsts) ->
      exists rhst1 rhst2,
        steps step_m sys st1 (List.concat (rhst2 ++ hst2 :: hst1 :: rhst1)) st2 /\
        BEquivalent sys (List.concat (hst2 :: hsts ++ [hst1]))
                    (List.concat (rhst2 ++ hst2 :: hst1 :: rhst1)) /\
        Forall (STransactional msg_dec) (rhst2 ++ rhst1) /\
        List.length hsts = List.length (rhst2 ++ rhst1).

  Lemma well_interleaved_reducible:
    forall (Hwi: WellInterleaved) trss st1 st2,
      steps step_m sys st1 (List.concat trss) st2 ->
      Forall (STransactional msg_dec) trss ->
      Interleaved trss ->
      exists (rhst : MHistory) (m : nat),
        steps step_m sys st1 rhst st2 /\
        BEquivalent sys (List.concat trss) rhst /\
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
    pose proof (Hwi _ _ _ _ _ H5 H2 H6 H3 H4).
    destruct H7 as [rhst1 [rhst2 [? [? [? ?]]]]].

    exists ((List.concat hsts3)
              ++ (List.concat (rhst2 ++ (hst2 ++ hst1) :: rhst1))
              ++ (List.concat hsts1)); eexists.
    split; [|split; [|split]].
    - eapply steps_append; eauto.
      eapply steps_append; eauto.
      replace (List.concat (rhst2 ++ (hst2 ++ hst1) :: rhst1))
        with (List.concat (rhst2 ++ hst2 :: hst1 :: rhst1)); [assumption|].
      repeat (rewrite concat_app; simpl).
      rewrite <-app_assoc; reflexivity.
    - red.
      repeat rewrite behaviorOf_app.
      do 2 f_equal.
      replace (List.concat (rhst2 ++ (hst2 ++ hst1) :: rhst1))
        with (List.concat (rhst2 ++ hst2 :: hst1 :: rhst1)); [assumption|].
      repeat (rewrite concat_app; simpl).
      rewrite <-app_assoc; reflexivity.
    - econstructor.
      + repeat rewrite <-concat_app; reflexivity.
      + reflexivity.
      + apply Forall_app_inv in H10; dest.
        repeat (apply Forall_app; auto).
        constructor; auto.
        eapply continuous_atomic_concat in H2; eauto.
        destruct H2 as [inits [ins [outs [eouts ?]]]].
        eapply STrsAtomic; eauto.
    - repeat (simpl; try rewrite app_length).
      unfold MHistory, History, MLabel in *; rewrite H13.
      apply plus_lt_compat_l.
      rewrite app_length.
      rewrite <-Nat.add_assoc; simpl.
      repeat rewrite Nat.add_succ_r.
      rewrite Nat.add_assoc.
      auto.
  Qed.

  Definition WellInterleavedPush :=
    forall st1 st2 hst1 hst2 hsts,
      steps step_m sys st1 (List.concat (hst2 :: hsts ++ [hst1])) st2 ->
      Continuous hst1 hst2 ->
      Forall (STransactional msg_dec) hsts ->
      Separated (hsts ++ [hst1]) ->
      Separated (hst2 :: hsts) ->
      exists (lpush rpush: MHistory -> Prop),
        rpush hst1 /\ lpush hst2 /\
        (forall lhst rhst,
            lpush lhst -> rpush rhst ->
            Reducible sys (lhst ++ rhst) (rhst ++ lhst)) /\
        Forall (fun hst => lpush hst \/ rpush hst) hsts.

  Lemma left_pushes_commutable:
    forall (lpush rpush: MHistory -> Prop),
      (forall lhst rhst,
          lpush lhst -> rpush rhst ->
          Reducible sys (lhst ++ rhst) (rhst ++ lhst)) ->
      forall rhst hsts,
        rpush rhst ->
        Forall lpush hsts ->
        Reducible sys (List.concat hsts ++ rhst) (rhst ++ List.concat hsts).
  Proof.
    induction hsts; simpl; intros;
      [rewrite app_nil_r; apply reducible_refl|].
    
    inv H1; specialize (IHhsts H0 H5).
    rewrite <-app_assoc.
    eapply reducible_trans.
    - apply reducible_app_1; eassumption.
    - do 2 rewrite app_assoc.
      apply reducible_app_2; auto.
  Qed.
      
  Lemma well_interleaved_push_ok:
    forall (Hwip: WellInterleavedPush), WellInterleaved.
  Proof.
    unfold WellInterleavedPush, WellInterleaved; intros.
    specialize (Hwip _ _ _ _ _ H H0 H1 H2 H3).
    destruct Hwip as [lpush [rpush ?]]; dest.
    
    generalize dependent st1; generalize dependent st2.
    generalize dependent hsts.
    intros hsts ?.
    eapply list_ind_pick
      with (l:= hsts) (Q0:= lpush) (Q1:= rpush); eauto; simpl; intros.

    - exists nil, nil.
      simpl in *; rewrite app_nil_r in *.
      repeat split; auto.
    - clear H7 hsts; rename l into hsts.
      exists hsts, nil.

      rewrite concat_app in H8; simpl in H8.
      rewrite app_nil_r in H8; simpl in H8.
      eapply steps_split in H8; [|reflexivity].
      destruct H8 as [sti [? ?]].
      
      assert (Reducible sys (List.concat hsts ++ hst1)
                        (hst1 ++ List.concat hsts))
        by (eapply left_pushes_commutable; eauto).

      simpl; repeat split; auto.
      + eapply steps_append; eauto.
        apply H9; auto.
      + red; do 2 rewrite behaviorOf_app.
        f_equal.
        rewrite concat_app; simpl.
        rewrite app_nil_r.
        eapply H9; eauto.
      
    - clear H7 hsts; rename l0 into hsts2; rename l1 into hsts1.

      apply Forall_app_inv in H3; dest; inv H7.
      specialize (H2 (Forall_app H3 H14)).
      replace ((hsts2 ++ a :: hsts1) ++ [hst1])
        with (hsts2 ++ a :: (hsts1 ++ [hst1])) in H8
        by (rewrite <-app_assoc; reflexivity).
      apply separated_cons with (hsts2:= hsts2) in H8; dest.
      rewrite app_assoc in H11.
      specialize (H2 H11).
      apply separated_cons with (hsts2:= hst2 :: hsts2) in H9; dest.
      specialize (H2 H15).

      replace (hst2 ++ List.concat ((hsts2 ++ a :: hsts1) ++ [hst1]))
        with (((hst2 ++ List.concat hsts2) ++ a) ++ List.concat hsts1 ++ hst1)
        in H10
        by (repeat rewrite concat_app;
            simpl; rewrite app_nil_r;
            repeat rewrite app_assoc; reflexivity).

      eapply steps_split in H10; [|reflexivity].
      destruct H10 as [sti [? ?]].

      assert (Reducible sys ((hst2 ++ List.concat hsts2) ++ a)
                        (a ++ hst2 ++ List.concat hsts2)).
      { change (hst2 ++ List.concat hsts2) with (List.concat (hst2 :: hsts2)).
        eapply left_pushes_commutable; eauto.
      }

      apply H17 in H16; dest.
      pose proof (steps_append H10 H16); clear H10 H16 sti.
      rewrite <-app_assoc in H19.
      eapply steps_split in H19; [|reflexivity].
      destruct H19 as [sti [? ?]].

      replace ((hst2 ++ List.concat hsts2) ++ List.concat hsts1 ++ hst1)
        with (hst2 ++ List.concat ((hsts2 ++ hsts1) ++ [hst1])) in H10
        by (repeat rewrite concat_app;
            simpl; rewrite app_nil_r;
            repeat rewrite app_assoc; reflexivity).

      specialize (H2 _ _ H10).
      destruct H2 as [rhst1 [rhst2 ?]]; dest.
      pose proof (steps_append H2 H16).

      exists rhst1, (a :: rhst2).
      repeat split; auto.
      + simpl; repeat rewrite concat_app.
        simpl; repeat rewrite app_nil_r.
        eapply bequivalent_trans.
        * repeat rewrite app_assoc.
          do 2 apply bequivalent_app_2.
          eassumption.
        * repeat rewrite <-app_assoc.
          apply bequivalent_app_1.
          repeat rewrite concat_app in H19.
          simpl in H19; repeat rewrite <-app_assoc in H19.
          rewrite app_nil_r in H19; assumption.
      + simpl; constructor; auto.
      + simpl; repeat rewrite app_length in *; simpl.
        rewrite Nat.add_succ_r; auto.
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
      right; apply well_interleaved_reducible; auto.
  Qed.

End WellInterleaved.

