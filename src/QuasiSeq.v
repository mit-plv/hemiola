Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT SemFacts.
Require Import Serial SerialFacts Reduction.

Require Import Omega Wf.

Set Implicit Arguments.

Open Scope list.

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
    Reachable (steps step_m) sys st1 /\
    steps step_m sys st1 (hst2 ++ hst ++ hst1) st2.

Definition Interleaved (hsts: list MHistory) :=
  exists hst1 hst2 hsts1 hsts2 hsts3,
    hsts = hsts3 ++ hst2 :: hsts2 ++ hst1 :: hsts1 /\
    Continuous hst1 hst2.

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
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall st2 hst1 hst2 hsts,
        steps step_m sys st1 (List.concat (hst2 :: hsts ++ [hst1])) st2 ->
        Continuous hst1 hst2 ->
        Forall (STransactional msg_dec) hsts ->
        exists rhst1 rhst2,
          steps step_m sys st1 (List.concat (rhst2 ++ hst2 :: hst1 :: rhst1)) st2 /\
          BEquivalent sys (List.concat (hst2 :: hsts ++ [hst1]))
                      (List.concat (rhst2 ++ hst2 :: hst1 :: rhst1)) /\
          Forall (STransactional msg_dec) (rhst2 ++ rhst1) /\
          List.length hsts = List.length (rhst2 ++ rhst1).

  Lemma well_interleaved_reducible:
    forall (Hwi: WellInterleaved) trss st1 st2
           (Hr: Reachable (steps step_m) sys st1),
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
    destruct H1 as [hst1 [hst2 [hsts1 [hsts2 [hsts3 ?]]]]]; dest; subst.
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
    inv H4; apply Forall_app_inv in H8; dest; inv H5.
    pose proof (Hwi _ (reachable_steps Hr H) _ _ _ _ H3 H2 H4).
    destruct H5 as [rhst1 [rhst2 ?]]; dest.

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
      + apply Forall_app_inv in H8; dest.
        repeat (apply Forall_app; auto).
        constructor; auto.
        eapply continuous_atomic_concat in H2; eauto.
        destruct H2 as [inits [ins [outs [eouts ?]]]].
        eapply STrsAtomic; eauto.
    - repeat (simpl; try rewrite app_length).
      unfold MHistory, History, MLabel in *; rewrite H11.
      apply plus_lt_compat_l.
      rewrite app_length.
      rewrite <-Nat.add_assoc; simpl.
      repeat rewrite Nat.add_succ_r.
      rewrite Nat.add_assoc.
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
      right; apply well_interleaved_reducible; auto.
      apply reachable_init.
  Qed.

End WellInterleaved.

Section WellInterleavedPush.
  Variable (sys: System).

  (* TODO: check whether [hsts2] is required. Enough just with adjacent histories? *)
  Definition LRPushable (lpush rpush: MHistory -> Prop) (hsts: list MHistory) :=
    forall lhst rhst hsts1 hsts2 hsts3,
      hsts = hsts3 ++ lhst :: hsts2 ++ rhst :: hsts1 ->
      lpush lhst -> rpush rhst ->
      Reducible sys (lhst ++ rhst) (rhst ++ lhst).

  Lemma LRPushable_split_left:
    forall lpush rpush hsts1 hsts2,
      LRPushable lpush rpush (hsts1 ++ hsts2) ->
      LRPushable lpush rpush hsts1.
  Proof.
  Admitted.

  Lemma LRPushable_commutable_left:
    forall lpush rpush hsts hst,
      LRPushable lpush rpush (hsts ++ [hst]) ->
      Forall lpush hsts ->
      rpush hst ->
      Reducible sys (List.concat hsts ++ hst) (hst ++ List.concat hsts).
  Proof.
  Admitted.

  Definition WellInterleavedPush :=
    forall hst1 hst2,
      ValidContinuous sys hst1 hst2 ->
      exists (lpush rpush: MHistory -> Prop),
        rpush hst1 /\ lpush hst2 /\
        forall st1,
          Reachable (steps step_m) sys st1 ->
          forall hsts st2,
            Forall (STransactional msg_dec) hsts ->
            steps step_m sys st1 (List.concat (hst2 :: hsts ++ [hst1])) st2 ->
            Forall (fun hst => lpush hst \/ rpush hst) hsts /\
            LRPushable lpush rpush (hsts ++ [hst1]) /\
            LRPushable lpush rpush (hst2 :: hsts).

  Lemma well_interleaved_push_ok:
    forall (Hwip: WellInterleavedPush), WellInterleaved sys.
  Proof.
    unfold WellInterleavedPush, WellInterleaved; intros.

    assert (ValidContinuous sys hst1 hst2) as Hvc.
    { simpl in H0; rewrite concat_app in H0.
      simpl in H0; rewrite app_nil_r in H0.
      red; split; eauto.
    }
    specialize (Hwip _ _ Hvc); clear Hvc.
    destruct Hwip as [lpush [rpush ?]]; dest.

    pose proof (H5 _ H _ _ H2 H0); dest.
    generalize dependent st1.
    generalize dependent st2.
    generalize H2.
    eapply list_ind_pick
      with (l:= hsts) (Q0:= lpush) (Q1:= rpush); eauto; simpl; intros.

    - exists nil, nil.
      simpl in *; rewrite app_nil_r in *.
      repeat split; auto.
    - clear H2 H6 H7 H8 hsts; rename l into hsts.
      exists hsts, nil.

      assert (Reducible sys (List.concat hsts ++ hst1)
                        (hst1 ++ List.concat hsts)).
      { specialize (H5 _ H9 _ _ H0 H10); dest.
        eapply LRPushable_commutable_left; eauto.
      }

      rewrite concat_app in H10; simpl in H10.
      rewrite app_nil_r in H10; simpl in H10.
      eapply steps_split in H10; [|reflexivity].
      destruct H10 as [sti [? ?]].

      simpl; repeat split; auto.
      + eapply steps_append; eauto.
        apply H2; auto.
      + red; do 2 rewrite behaviorOf_app.
        f_equal.
        rewrite concat_app; simpl.
        rewrite app_nil_r.
        eapply H2; eauto.
      
    - clear H2 H6 H7 H8 hsts; rename l0 into hsts2; rename l1 into hsts1.

      assert (Reducible sys ((hst2 ++ List.concat hsts2) ++ a)
                        (a ++ hst2 ++ List.concat hsts2)).
      { specialize (H5 _ H11 _ _ H10 H12); dest.
        change (hst2 ++ List.concat hsts2) with (List.concat (hst2 :: hsts2)).
        eapply LRPushable_commutable_left; eauto.
        eapply LRPushable_split_left with (hsts2:= hsts1).
        rewrite <-app_assoc; assumption.
      }

      apply Forall_app_inv in H10; dest; inv H7.
      specialize (H9 (Forall_app H6 H14)).

      replace (hst2 ++ List.concat ((hsts2 ++ a :: hsts1) ++ [hst1]))
        with (((hst2 ++ List.concat hsts2) ++ a) ++ List.concat hsts1 ++ hst1)
        in H12
        by (repeat rewrite concat_app;
            simpl; rewrite app_nil_r;
            repeat rewrite app_assoc; reflexivity).
      eapply steps_split in H12; [|reflexivity].
      destruct H12 as [sti [? ?]].
      apply H2 in H8; dest.
      pose proof (steps_append H7 H8); clear H7 H8 sti.
      rewrite <-app_assoc in H12.
      eapply steps_split in H12; [|reflexivity].
      destruct H12 as [sti [? ?]].
      replace ((hst2 ++ List.concat hsts2) ++ List.concat hsts1 ++ hst1)
        with (hst2 ++ List.concat ((hsts2 ++ hsts1) ++ [hst1])) in H7
        by (repeat rewrite concat_app;
            simpl; rewrite app_nil_r;
            repeat rewrite app_assoc; reflexivity).
      specialize (H9 _ _ H11 H7).
      destruct H9 as [rhst1 [rhst2 ?]]; dest.
      pose proof (steps_append H9 H8).

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
          repeat rewrite concat_app in H12.
          simpl in H12; repeat rewrite <-app_assoc in H12.
          rewrite app_nil_r in H12; assumption.
      + simpl; constructor; auto.
      + simpl; repeat rewrite app_length in *; simpl.
        rewrite Nat.add_succ_r; auto.
  Qed.

End WellInterleavedPush.

Close Scope list.

