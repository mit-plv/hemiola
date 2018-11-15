Require Import Bool List String Peano_dec FinFun.
Require Import Common FMap Syntax Semantics SemFacts Invariant StepT.

Set Implicit Arguments.

Open Scope list.

Section Simulation.
  Context {SystemI StateI LabelI SystemS StateS LabelS: Type}
          `{HasInit SystemI StateI} `{HasLabel LabelI}
          `{HasInit SystemS StateS} `{HasLabel LabelS}.
  Variables (stepI: Step SystemI StateI LabelI) (stepS: Step SystemS StateS LabelS)
            (sim: StateI -> StateS -> Prop).

  Local Infix "≈" := sim (at level 30).

  Variables (impl: SystemI) (spec: SystemS).

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
  Context {SystemI StateI LabelI SystemS StateS LabelS: Type}
          `{HasInit SystemI StateI} `{HasLabel LabelI}
          `{HasInit SystemS StateS} `{HasLabel LabelS}.
  Variables (stepI: Step SystemI StateI LabelI) (stepS: Step SystemS StateS LabelS)
            (ginv: StateI -> Prop)
            (sim: StateI -> StateS -> Prop).

  Local Infix "≈" := sim (at level 30).
  
  Variables (impl: SystemI) (spec: SystemS).

  Definition InvSim :=
    forall ist1 sst1,
      Reachable (steps stepI) impl ist1 ->
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

  Hypotheses (Hsim: InvSim)
             (Hinv: InvStep impl stepI ginv)
             (Hsimi: sim (initsOf impl) (initsOf spec))
             (Hinvi: ginv (initsOf impl)).

  Lemma inv_simulation_steps:
    forall ihst ist1 ist2,
      ist1 = initsOf impl ->
      steps stepI impl ist1 ihst ist2 ->
      exists sst2 shst,
        steps stepS spec (initsOf spec) shst sst2 /\
        behaviorOf ihst = behaviorOf shst /\
        ist2 ≈ sst2.
  Proof.
    induction 2; simpl; intros; subst;
      [exists (initsOf spec), nil; repeat split; auto; constructor|].

    specialize (IHsteps eq_refl).
    destruct IHsteps as [sst2 [shst [? [? ?]]]].

    eapply Hsim in H5;
      [|red; eauto
       |eassumption
       |eapply inv_steps with (LabelI:= LabelI); eassumption].
    
    destruct (getLabel lbl) as [elbl|].

    - destruct H5 as [sst3 [slbl [? [? ?]]]].
      eexists; eexists (_ :: _); repeat split; eauto.
      + econstructor; eauto.
      + simpl; erewrite H6, H8; simpl.
        reflexivity.
    - destruct H5.
      * destruct H5 as [sst3 [slbl [? [? ?]]]].
        eexists; eexists (slbl :: _); repeat split; eauto.
        -- econstructor; eauto.
        -- simpl; rewrite H6, H8; simpl; reflexivity.
      * exists sst2, shst; repeat split; auto.
  Qed.

  Theorem invSim_implies_refinement:
    (steps stepI) # (steps stepS) |-- impl ⊑ spec.
  Proof.
    unfold Simulates, Refines; intros.
    inv H3.
    eapply inv_simulation_steps in H4; [|reflexivity].
    destruct H4 as [sst2 [shst [? [? ?]]]].
    econstructor; eauto.
  Qed.
  
End InvSim.

Definition liftSim {iifc sifc} (ossSim: OStates iifc -> OStates sifc -> Prop):
  MState iifc -> MState sifc -> Prop :=
  fun ist sst => ossSim (bst_oss ist) (bst_oss sst).

Close Scope list.

