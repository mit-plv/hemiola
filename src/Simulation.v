Require Import Bool List String Peano_dec FinFun.
Require Import Common FMap Syntax Semantics SemFacts Invariant StepT.

Set Implicit Arguments.

Section Simulation.
  Context {SysI SysS StateI LabelI StateS LabelS: Type}
          `{IsSystem SysI} `{HasInit SysI StateI} `{HasLabel LabelI}
          `{IsSystem SysS} `{HasInit SysS StateS} `{HasLabel LabelS}.
  Variables (stepI: Step SysI StateI LabelI) (stepS: Step SysS StateS LabelS)
            (sim: StateI -> StateS -> Prop).

  Local Infix "≈" := sim (at level 30).

  Variables (impl: SysI) (spec: SysS).

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
          behaviorOf impl ihst = behaviorOf spec shst /\
          ist2 ≈ sst2.
  Proof.
    induction 2; simpl; intros;
      [exists sst1, nil; repeat split; auto; constructor|].

    specialize (IHsteps H5).
    destruct IHsteps as [sst2 [shst [? [? ?]]]].

    eapply Hsim in H7; [|exact H10].
    destruct (getLabel lbl) as [elbl|].

    - destruct H7 as [sst3 [slbl [? [? ?]]]].
      eexists; eexists (_ :: _); repeat split; eauto.
      + econstructor; eauto.
      + simpl; erewrite H9, H11; simpl.
        reflexivity.
    - destruct H7.
      * destruct H7 as [sst3 [slbl [? [? ?]]]].
        eexists; eexists (slbl :: _); repeat split; eauto.
        -- econstructor; eauto.
        -- simpl; rewrite H9, H11; simpl; reflexivity.
      * exists sst2, shst; repeat split; auto.
  Qed.

  Hypothesis (Hsimi: sim (initsOf impl) (initsOf spec)).

  Theorem simulation_implies_refinement:
    (steps stepI) # (steps stepS) |-- impl ⊑ spec.
  Proof.
    unfold Simulates, Refines; intros.
    inv H5.
    eapply simulation_steps in H6; [|exact Hsimi].
    destruct H6 as [sst2 [shst [? [? ?]]]].
    econstructor; eauto.
  Qed.

End Simulation.

Section InvSim.
  Context {SysI SysS StateI LabelI StateS LabelS: Type}
          `{IsSystem SysI} `{HasInit SysI StateI} `{HasLabel LabelI}
          `{IsSystem SysS} `{HasInit SysS StateS} `{HasLabel LabelS}.
  Variables (stepI: Step SysI StateI LabelI) (stepS: Step SysS StateS LabelS)
            (ginv: StateI -> Prop)
            (sim: StateI -> StateS -> Prop)
            (linv: LabelI -> Prop).

  Local Infix "≈" := sim (at level 30).
  
  Variables (impl: SysI) (spec: SysS).

  Definition InvSim :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      ginv ist1 ->
      forall ilbl ist2,
        linv ilbl ->
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
        Forall linv ihst ->
        steps stepI impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps stepS spec sst1 shst sst2 /\
          behaviorOf impl ihst = behaviorOf spec shst /\
          ist2 ≈ sst2.
  Proof.
    induction 4; simpl; intros;
      [exists sst1, nil; repeat split; auto; constructor|].

    inv H7.
    specialize (IHsteps H5 H6 H13).
    destruct IHsteps as [sst2 [shst [? [? ?]]]].

    eapply Hsim in H9;
      [|exact H11|eapply inv_steps; eauto|exact H12].
    
    destruct (getLabel lbl) as [elbl|].

    - destruct H9 as [sst3 [slbl [? [? ?]]]].
      eexists; eexists (_ :: _); repeat split; eauto.
      + econstructor; eauto.
      + simpl; erewrite H10, H14; simpl.
        reflexivity.
    - destruct H9.
      * destruct H9 as [sst3 [slbl [? [? ?]]]].
        eexists; eexists (slbl :: _); repeat split; eauto.
        -- econstructor; eauto.
        -- simpl; rewrite H10, H14; simpl; reflexivity.
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

Definition ImpliesSimMP (sim: TState -> TState -> Prop) :=
  forall ist sst,
    sim ist sst ->
    tst_msgs sst = tst_trss ist.

Section NoRules.

  Lemma steps_simulation_BlockedInv_SimMP_no_rules:
    forall (sim: TState -> TState -> Prop) impl spec,
      merqsOf impl = merqsOf spec ->
      merssOf impl = merssOf spec ->
      MsgsSim sim ->
      ImpliesSimMP sim ->
      sys_rules impl = nil ->
      forall ist1 sst1,
        sim ist1 sst1 ->
        forall ihst ist2,
          steps step_t impl ist1 ihst ist2 ->
          exists (sst2 : TState) (shst : list TLabel),
            steps step_t spec sst1 shst sst2 /\
            behaviorOf impl ihst = behaviorOf spec shst /\
            sim ist2 sst2.
  Proof.
    induction 7; simpl; intros;
      [do 2 eexists; repeat split; [constructor|reflexivity|assumption]|].

    specialize (IHsteps H4); dest.
    inv H6.
    - do 2 eexists; repeat split; eauto.
    - destruct x as [noss norqs nmsgs ntid].
      do 2 eexists; repeat split.
      + eapply StepsCons.
        * eassumption.
        * eapply StIns; eauto.
          eapply ValidMsgsExtIn_merqsOf; eauto.
      + simpl; rewrite <-H8; reflexivity.
      + eapply H1; eauto.
    - destruct x as [noss norqs nmsgs ntid].
      do 2 eexists; repeat split.
      + eapply StepsCons.
        * eassumption.
        * eapply StOuts; try reflexivity; try eassumption.
          { (* first-to-first: requires an invariant about [SimMP] *)
            admit.
          }
          { eapply ValidMsgsExtOut_merssOf; eauto. }
      + simpl; rewrite <-H8; reflexivity.
      + eapply H1; eauto.
    - exfalso.
      rewrite H3 in H17; elim H17.
  Admitted.

End NoRules.

