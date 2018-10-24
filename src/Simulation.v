Require Import Bool List String Peano_dec FinFun.
Require Import Common FMap Syntax Semantics SemFacts Invariant StepT.

Set Implicit Arguments.

Section Simulation.
  Context {StateI LabelI StateS LabelS: Type}
          `{HasInit System StateI} `{HasLabel LabelI}
          `{HasInit System StateS} `{HasLabel LabelS}.
  Variables (stepI: Step StateI LabelI) (stepS: Step StateS LabelS)
            (sim: StateI -> StateS -> Prop).

  Local Infix "≈" := sim (at level 30).

  Variables (impl spec: System).

  Definition Simulates :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ilbl ist2,
        stepI impl ist1 ilbl ist2 ->
        match getLabel ilbl with
        | None => (exists sst2 slbl,
                      stepS spec sst1 slbl sst2 /\
                      getLabel slbl = None /\
                      ist2 ≈ sst2) \/
                  ist2 ≈ sst1
        | Some elbl => (exists sst2 slbl,
                           stepS spec sst1 slbl sst2 /\
                           getLabel slbl = Some elbl /\
                           ist2 ≈ sst2)
        end.

  Hypothesis (Hsim: Simulates).

  Lemma simulation_steps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ihst ist2,
        steps stepI impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps stepS spec sst1 shst sst2 /\
          behaviorOf ihst = behaviorOf shst /\
          ist2 ≈ sst2.
  Proof.
    induction 2; simpl; intros;
      [exists sst1, nil; repeat split; auto; constructor|].

    specialize (IHsteps H3).
    destruct IHsteps as [sst2 [shst [? [? ?]]]].

    eapply Hsim in H5; [|exact H8].
    destruct (getLabel lbl) as [elbl|].

    - destruct H5 as [sst3 [slbl [? [? ?]]]].
      eexists; eexists (_ :: _); repeat split; eauto.
      + econstructor; eauto.
      + simpl; erewrite H7, H9; simpl.
        reflexivity.
    - destruct H5.
      * destruct H5 as [sst3 [slbl [? [? ?]]]].
        eexists; eexists (slbl :: _); repeat split; eauto.
        -- econstructor; eauto.
        -- simpl; rewrite H7, H9; simpl; reflexivity.
      * exists sst2, shst; repeat split; auto.
  Qed.

  Hypothesis (Hsimi: sim (initsOf impl) (initsOf spec)).

  Theorem simulation_implies_refinement:
    (steps stepI) # (steps stepS) |-- impl ⊑ spec.
  Proof.
    unfold Simulates, Refines; intros.
    inv H3.
    eapply simulation_steps in H4; [|exact Hsimi].
    destruct H4 as [sst2 [shst [? [? ?]]]].
    econstructor; eauto.
  Qed.

End Simulation.

Section InvSim.
  Context {StateI LabelI StateS LabelS: Type}
          `{HasInit System StateI} `{HasLabel LabelI}
          `{HasInit System StateS} `{HasLabel LabelS}.
  Variables (stepI: Step StateI LabelI) (stepS: Step StateS LabelS)
            (ginv: StateI -> Prop)
            (sim: StateI -> StateS -> Prop).

  Local Infix "≈" := sim (at level 30).
  
  Variables (impl spec: System).

  Definition InvSim :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall ilbl ist2,
        stepI impl ist1 ilbl ist2 ->
        match getLabel ilbl with
        | None =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              getLabel slbl = None /\
              ist2 ≈ sst2) \/
          ist2 ≈ sst1
        | Some elbl =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              getLabel slbl = Some elbl /\
              ist2 ≈ sst2)
        end.

  Hypothesis (Hsim: InvSim)
             (Hinv: InvStep impl stepI ginv).

  Lemma inv_simulation_steps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall ihst ist2,
        steps stepI impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps stepS spec sst1 shst sst2 /\
          behaviorOf ihst = behaviorOf shst /\
          ist2 ≈ sst2.
  Proof.
    induction 3; simpl; intros;
      [exists sst1, nil; repeat split; auto; constructor|].

    specialize (IHsteps H3 H4).
    destruct IHsteps as [sst2 [shst [? [? ?]]]].

    eapply Hsim in H6;
      [|exact H9|eapply inv_steps; eauto].
    
    destruct (getLabel lbl) as [elbl|].

    - destruct H6 as [sst3 [slbl [? [? ?]]]].
      eexists; eexists (_ :: _); repeat split; eauto.
      + econstructor; eauto.
      + simpl; erewrite H8, H10; simpl.
        reflexivity.
    - destruct H6.
      * destruct H6 as [sst3 [slbl [? [? ?]]]].
        eexists; eexists (slbl :: _); repeat split; eauto.
        -- econstructor; eauto.
        -- simpl; rewrite H8, H10; simpl; reflexivity.
      * exists sst2, shst; repeat split; auto.
  Qed.

End InvSim.

Definition LiftInv {StateT1 StateT2} (f: StateT2 -> StateT1)
           (inv: StateT1 -> Prop): StateT2 -> Prop :=
  fun st2 => inv (f st2).
  
Definition LiftSimL {StateI1 StateI2} (f: StateI2 -> StateI1)
           {StateS} (sim: StateI1 -> StateS -> Prop): StateI2 -> StateS -> Prop :=
  fun sti2 sts => sim (f sti2) sts.

Definition LiftSimR {StateS1 StateS2} (f: StateS2 -> StateS1)
           {StateI} (sim: StateI -> StateS1 -> Prop): StateI -> StateS2 -> Prop :=
  fun sti sts2 => sim sti (f sts2).

Definition MsgsSim (sim: TState -> TState -> Prop) :=
  forall ioss iorqs imsgs imsgs' itrss itrss' its
         soss sorqs smsgs smsgs' strss strss' sts,
    sim {| tst_oss := ioss; tst_orqs := iorqs;
           tst_msgs := imsgs; tst_trss := itrss; tst_tid := its |}
        {| tst_oss := soss; tst_orqs := sorqs;
           tst_msgs := smsgs; tst_trss := strss; tst_tid := sts |} ->
    sim {| tst_oss := ioss; tst_orqs := iorqs;
           tst_msgs := imsgs'; tst_trss := itrss'; tst_tid := its |}
        {| tst_oss := soss; tst_orqs := sorqs;
           tst_msgs := smsgs'; tst_trss := strss'; tst_tid := sts |}.

Definition SimMP (ist sst: TState): Prop :=
  tst_msgs sst = tst_trss ist.

Definition ImpliesSimMP (sim: TState -> TState -> Prop) :=
  forall ist sst, sim ist sst -> SimMP ist sst.

