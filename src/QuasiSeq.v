Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT SemFacts.
Require Import Serial SerialFacts Reduction.

Require Import Omega Wf.

Set Implicit Arguments.

Open Scope list.

(*! Quasi-sequential histories *)

Section QuasiSeq.
  Context {oifc: OStateIfc}.
  Variables (sys: System oifc)
            (quasiSeq: forall (sys: System oifc) (hst: MHistory) (n: nat), Prop).

  Definition QuasiSeqOkInit :=
    forall hst st,
      steps step_m sys (initsOf sys) hst st ->
      exists n, quasiSeq sys hst n.

  Definition QuasiSeqOkStep :=
    forall hst n st,
      steps step_m sys (initsOf sys) hst st ->
      quasiSeq sys hst n ->
      ((exists rhst rtrss,
           steps step_m sys (initsOf sys) rhst st /\
           Sequential sys msg_dec rhst rtrss) \/
       (exists rhst m,
           steps step_m sys (initsOf sys) rhst st /\
           quasiSeq sys rhst m /\ m < n)).

  Lemma quasiSeq_implies_serializableSys:
    QuasiSeqOkStep ->
    forall n hst st,
      steps step_m sys (initsOf sys) hst st ->
      quasiSeq sys hst n ->
      Serializable sys hst st.
  Proof.
    induction n as [n IHn] using (well_founded_induction lt_wf).
    intros.
    specialize (H _ _ _ H0 H1); destruct H.
    - destruct H as [rhst [rtrss [? ?]]].
      exists rhst; split; eauto.
    - destruct H as [rhst [m ?]]; dest.
      specialize (IHn _ H3 _ _ H H2).
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

Definition ValidContinuous {oifc} (sys: System oifc) (hst1 hst2: MHistory) :=
  Continuous hst1 hst2 /\
  exists st1 st2 hst,
    Reachable (steps step_m) sys st1 /\
    steps step_m sys st1 (hst2 ++ hst ++ hst1) st2.

Definition Interleaved (hsts: list MHistory) :=
  exists hst1 hst2 hsts1 hsts2 hsts3,
    hsts = hsts3 ++ hst2 :: hsts2 ++ hst1 :: hsts1 /\
    Continuous hst1 hst2 /\
    Forall (fun hst => ~ Continuous hst1 hst) hsts2 /\
    Forall (fun hst => ~ Continuous hst hst2) hsts2.

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

Lemma atomic_trss_sequential_or_interleaved:
  forall {oifc} (sys: System oifc) trss st1 st2,
    Reachable (steps step_m) sys st1 ->
    steps step_m sys st1 (List.concat trss) st2 ->
    Forall (AtomicEx msg_dec) trss ->
    Sequential sys msg_dec (List.concat trss) trss \/
    Interleaved trss.
Proof.
  induction trss as [|trs trss]; simpl; intros;
    [left; constructor; auto|].

  eapply steps_split in H0; [|reflexivity].
  destruct H0 as [sti [? ?]].
  inv H1.
  specialize (IHtrss _ _ H H0 H6); destruct IHtrss.

  - (* TODO: need to prove that whenever an atomic
     * [Atomic inits ins trs outs eouts] is added to a history ([List.concat trss]),
     * [inits] is either a new semi-transaction or a continuation from one of 
     * previous semi-transactions.
     *
     * This is not true when [inits] takes a part from [trs1] and the other part
     * from [trs2], where [trs1 <> trs2] and [trs1 ∈ trss /\ trs2 ∈ trss].
     * Thus we need a static condition to ensure each rule in the system takes
     * incoming messages for a single transaction.
     *)
    admit.
  - right.
    clear -H1.
    destruct H1 as [hst1 [hst2 [hsts1 [hsts2 [hsts3 [? ?]]]]]]; subst.
    exists hst1, hst2, hsts1, hsts2, (trs :: hsts3).
    split; auto.
Admitted.

Section WellInterleaved.
  Context {oifc: OStateIfc}.
  Variable (sys: System oifc).

  Definition WellInterleaved :=
    forall st1,
      Reachable (steps step_m) sys st1 ->
      forall st2 hst1 hst2 hsts,
        steps step_m sys st1 (List.concat (hst2 :: hsts ++ [hst1])) st2 ->
        Continuous hst1 hst2 ->
        Forall (fun hst => ~ Continuous hst1 hst) hsts ->
        Forall (fun hst => ~ Continuous hst hst2) hsts ->
        Forall (AtomicEx msg_dec) hsts ->
        exists rhst1 rhst2,
          steps step_m sys st1 (List.concat (rhst2 ++ hst2 :: hst1 :: rhst1)) st2 /\
          Forall (AtomicEx msg_dec) (rhst2 ++ rhst1) /\
          List.length hsts = List.length (rhst2 ++ rhst1).

  Lemma well_interleaved_reducible:
    forall (Hwi: WellInterleaved) trss st1 st2
           (Hr: Reachable (steps step_m) sys st1),
      steps step_m sys st1 (List.concat trss) st2 ->
      Forall (AtomicEx msg_dec) trss ->
      Interleaved trss ->
      exists (rhst : MHistory) (m : nat),
        steps step_m sys st1 rhst st2 /\
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
    inv H6; apply Forall_app_inv in H10; dest; inv H7.
    pose proof (Hwi _ (reachable_steps Hr H) _ _ _ _ H5 H2 H3 H4 H6).
    destruct H7 as [rhst1 [rhst2 ?]]; dest.

    exists ((List.concat hsts3)
              ++ (List.concat (rhst2 ++ (hst2 ++ hst1) :: rhst1))
              ++ (List.concat hsts1)); eexists.
    split; [|split].
    - eapply steps_append; eauto.
      eapply steps_append; eauto.
      replace (List.concat (rhst2 ++ (hst2 ++ hst1) :: rhst1))
        with (List.concat (rhst2 ++ hst2 :: hst1 :: rhst1)); [assumption|].
      repeat (rewrite concat_app; simpl).
      rewrite <-app_assoc; reflexivity.
    - econstructor.
      + repeat rewrite <-concat_app; reflexivity.
      + reflexivity.
      + apply Forall_app_inv in H8; dest.
        repeat (apply Forall_app; auto).
        * apply atomicEx_stransactional_forall; auto.
        * apply atomicEx_stransactional_forall; auto.
        * constructor; auto.
          { eapply continuous_atomic_concat in H2; eauto.
            destruct H2 as [inits [ins [outs [eouts ?]]]].
            eapply STrsAtomic; eauto.
          }
          { apply atomicEx_stransactional_forall; auto. }
        * apply atomicEx_stransactional_forall; auto.
    - repeat (simpl; try rewrite app_length).
      unfold MHistory, History, MLabel in *; rewrite H10.
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

      apply trss_reducible_to_ins_atomics_outs with (sys0:= sys) in H4.
      destruct H4 as [ins [atms [outs ?]]]; dest.

      pose proof (H4 _ _ H0).
      eapply steps_split in H6; [|reflexivity]; destruct H6 as [sti2 [? ?]].
      eapply steps_split in H6; [|reflexivity]; destruct H6 as [sti1 [? ?]].

      assert (Reachable (steps step_m) sys sti1) by (red; eauto).
      pose proof (atomic_trss_sequential_or_interleaved H9 H8 H2).
      destruct H10.
      + left.
        exists (outs ++ List.concat atms ++ ins).
        eexists (_ ++ atms ++ _).
        split.
        * apply H4; auto.
        * apply sequential_app; [apply sequential_outsHistory; assumption|].
          apply sequential_app; [|apply sequential_insHistory; assumption].
          assumption.
      + right.
        eapply well_interleaved_reducible with (st1:= sti1) in H; eauto.
        destruct H as [ratms [rm ?]]; dest.
        exists (outs ++ ratms ++ ins), (List.length outs + rm + List.length ins).
        split; [|split].
        * do 2 (eapply steps_append; eauto).
        * replace (List.length outs + rm + List.length ins)
            with (List.length outs + (rm + List.length ins)) by omega.
          apply ssequential_app; [apply ssequential_outsHistory; assumption|].
          apply ssequential_app; [|apply ssequential_insHistory; assumption].
          assumption.
        * unfold History, MLabel in H5, H12; omega.
  Qed.

End WellInterleaved.

Section WellInterleavedPush.
  Context {oifc: OStateIfc}.
  Variable (sys: System oifc).

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
    unfold LRPushable; intros; subst.
    eapply H; eauto.
    instantiate (1:= hsts0 ++ hsts2).
    instantiate (1:= hsts3).
    instantiate (1:= hsts4).
    repeat (rewrite <-app_assoc; simpl).
    reflexivity.
  Qed.

  Lemma LRPushable_split_right:
    forall lpush rpush hsts1 hsts2,
      LRPushable lpush rpush (hsts1 ++ hsts2) ->
      LRPushable lpush rpush hsts2.
  Proof.
    unfold LRPushable; intros; subst.
    eapply H; eauto.
    instantiate (1:= hsts0).
    instantiate (1:= hsts3).
    instantiate (1:= hsts1 ++ hsts4).
    repeat (rewrite <-app_assoc; simpl).
    reflexivity.
  Qed.

  Lemma LRPushable_commutable_left:
    forall lpush rpush hsts hst,
      LRPushable lpush rpush (hsts ++ [hst]) ->
      Forall lpush hsts ->
      rpush hst ->
      Reducible sys (List.concat hsts ++ hst) (hst ++ List.concat hsts).
  Proof.
    induction hsts; simpl; intros;
      [rewrite app_nil_r; apply reducible_refl|].

    inv H0.
    eapply reducible_trans.
    - rewrite <-app_assoc.
      apply reducible_app_1.
      apply IHhsts; auto.
      apply LRPushable_split_right with (hsts1:= [a]); auto.
    - do 2 rewrite app_assoc.
      apply reducible_app_2.
      eapply H; eauto.
      instantiate (1:= nil).
      instantiate (1:= hsts).
      instantiate (1:= nil).
      reflexivity.
  Qed.

  Definition WellInterleavedPush :=
    forall hst1 hst2,
      ValidContinuous sys hst1 hst2 ->
      exists (lpush rpush: MHistory -> Prop),
        rpush hst1 /\ lpush hst2 /\
        forall st1,
          Reachable (steps step_m) sys st1 ->
          forall hsts st2,
            Forall (AtomicEx msg_dec) hsts ->
            steps step_m sys st1 (List.concat (hst2 :: hsts ++ [hst1])) st2 ->
            Forall (fun hst => ~ Continuous hst1 hst) hsts ->
            Forall (fun hst => ~ Continuous hst hst2) hsts ->
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

    pose proof (H7 _ H _ _ H4 H0 H2 H3); dest.
    generalize dependent st1.
    generalize dependent st2.
    generalize H2 H3 H4.
    eapply list_ind_pick
      with (l:= hsts) (Q0:= lpush) (Q1:= rpush); eauto; simpl; intros.

    - exists nil, nil.
      simpl in *; rewrite app_nil_r in *.
      repeat split; auto.
    - clear H2 H3 H4 H8 H9 H10 hsts; rename l into hsts.
      exists hsts, nil.

      assert (Reducible sys (List.concat hsts ++ hst1)
                        (hst1 ++ List.concat hsts)).
      { specialize (H7 _ H13 _ _ H12 H14 H0 H11); dest.
        eapply LRPushable_commutable_left; eauto.
      }

      rewrite concat_app in H14; simpl in H14.
      rewrite app_nil_r in H14; simpl in H14.
      eapply steps_split in H14; [|reflexivity].
      destruct H14 as [sti [? ?]].

      simpl; repeat split; auto.
      eapply steps_append; eauto.
      
    - clear H2 H3 H4 H8 H9 H10 hsts; rename l0 into hsts2; rename l1 into hsts1.

      assert (Reducible sys ((hst2 ++ List.concat hsts2) ++ a)
                        (a ++ hst2 ++ List.concat hsts2)).
      { specialize (H7 _ H15 _ _ H14 H16 H12 H13); dest.
        change (hst2 ++ List.concat hsts2) with (List.concat (hst2 :: hsts2)).
        eapply LRPushable_commutable_left; eauto.
        eapply LRPushable_split_left with (hsts2:= hsts1).
        rewrite <-app_assoc; assumption.
      }

      apply Forall_app_inv in H12; dest; inv H4.
      apply Forall_app_inv in H13; dest; inv H8.
      apply Forall_app_inv in H14; dest; inv H9.
      specialize (H11 (Forall_app H3 H12) (Forall_app H4 H18) (Forall_app H8 H20)).

      replace (hst2 ++ List.concat ((hsts2 ++ a :: hsts1) ++ [hst1]))
        with (((hst2 ++ List.concat hsts2) ++ a) ++ List.concat hsts1 ++ hst1)
        in H16
        by (repeat rewrite concat_app;
            simpl; rewrite app_nil_r;
            repeat rewrite app_assoc; reflexivity).
      eapply steps_split in H16; [|reflexivity].
      destruct H16 as [sti [? ?]].

      apply H2 in H13.
      pose proof (steps_append H9 H13); clear H9 H13 sti.
      rewrite <-app_assoc in H14.
      eapply steps_split in H14; [|reflexivity].
      destruct H14 as [sti [? ?]].
      replace ((hst2 ++ List.concat hsts2) ++ List.concat hsts1 ++ hst1)
        with (hst2 ++ List.concat ((hsts2 ++ hsts1) ++ [hst1])) in H9
        by (repeat rewrite concat_app;
            simpl; rewrite app_nil_r;
            repeat rewrite app_assoc; reflexivity).
      specialize (H11 _ _ H15 H9).
      destruct H11 as [rhst1 [rhst2 ?]]; dest.
      pose proof (steps_append H11 H13).

      exists rhst1, (a :: rhst2).
      repeat split; auto.
      + simpl; constructor; auto.
      + simpl; repeat rewrite app_length in *; simpl.
        rewrite Nat.add_succ_r; auto.
  Qed.

End WellInterleavedPush.

Close Scope list.

