Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.

Section Simulation.

  Variables (step: System -> State -> Label -> State -> Prop)
            (sim: State -> State -> Prop)
            (p: BLabel -> BLabel).

  Local Infix "≈" := sim (at level 30).

  Variables (impl spec: System).

  Definition Simulates :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ilbl ist2,
        step impl ist1 ilbl ist2 ->
        match toBLabel ilbl with
        | Some b =>
          exists sst2 slbl, step spec sst1 slbl sst2 /\
                            toBLabel slbl = Some (p b) /\
                            ist2 ≈ sst2
        | None =>
          (exists sst2 slbl, step spec sst1 slbl sst2 /\
                             toBLabel slbl = None /\
                             ist2 ≈ sst2) \/
          ist2 ≈ sst1
        end.

  Hypothesis (Hsim: Simulates).

  Lemma simulation_steps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ihst ist2,
        steps step impl ist1 ihst ist2 ->
        exists sst2 shst,
          map p (behaviorOf ihst) = behaviorOf shst /\
          steps step spec sst1 shst sst2 /\
          ist2 ≈ sst2.
  Proof.
    induction 2; simpl; intros;
      [exists sst1, nil; repeat split; auto; constructor|].

    specialize (IHsteps H).
    destruct IHsteps as [sst2 [shst [? [? ?]]]].

    eapply Hsim in H1; [|exact H4].
    remember (toBLabel lbl) as blbl; destruct blbl as [blbl|]; simpl.

    - destruct H1 as [sst3 [slbl [? [? ?]]]].
      eexists; eexists (slbl :: _); repeat split; eauto.
      + simpl; rewrite H2, H5; simpl; reflexivity.
      + econstructor; eauto.
    - destruct H1.
      * destruct H1 as [sst3 [slbl [? [? ?]]]].
        eexists; eexists (slbl :: _); repeat split; eauto.
        -- simpl; rewrite H2, H5; simpl; reflexivity.
        -- econstructor; eauto.
      * exists sst2, shst; repeat split; auto.
  Qed.

  Hypothesis (Hsimi: sim (getStateInit impl) (getStateInit spec)).

  Theorem simulation_implies_refinement: step |-- impl ⊑[p] spec.
  Proof.
    unfold Simulates, Refines; intros.
    inv H.
    eapply simulation_steps in H0; [|exact Hsimi].
    destruct H0 as [? [? [? [? ?]]]].
    econstructor; eauto.
  Qed.

End Simulation.

