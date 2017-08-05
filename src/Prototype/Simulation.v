Require Import Bool List String Peano_dec.
Require Import FnMap Language.

Section Simulation.
  Context {MsgT IStateT SStateT: Type}.
  Context {MvalT: MsgT -> RqRs -> Type}.
  Hypothesis (msgT_dec : forall m1 m2 : MsgT, {m1 = m2} + {m1 <> m2}).
  Local Notation IState := (State MvalT IStateT).
  Local Notation SState := (State MvalT SStateT).

  Variable sim: IState -> SState -> Prop.
  Local Infix "≈" := sim (at level 30).

  Variables (impl: System MvalT IStateT)
            (spec: System MvalT SStateT).

  Definition Simulates :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ilbl ist2,
        step impl ist1 ilbl ist2 ->
        match getBLabel impl ilbl with
        | Some b =>
          exists sst2 slbl, step spec sst1 slbl sst2 /\
                            getBLabel spec slbl = Some b /\
                            ist2 ≈ sst2
        | None =>
          (exists sst2 slbl, step spec sst1 slbl sst2 /\
                             getBLabel spec slbl = None /\
                             ist2 ≈ sst2) \/
          ist2 ≈ sst1
        end.

  Hypothesis (Hsim: Simulates).

  Lemma simulation_steps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ihst ist2,
        steps impl ist1 ihst ist2 ->
        exists sst2 shst,
          behaviorOf impl ihst = behaviorOf spec shst /\
          steps spec sst1 shst sst2 /\
          ist2 ≈ sst2.
  Proof.
    induction 2; simpl; intros;
      [exists sst1, nil; repeat split; auto; constructor|].

    specialize (IHsteps H).
    destruct IHsteps as [sst2 [shst [? [? ?]]]].

    eapply Hsim in H1; [|exact H4].
    remember (getBLabel impl lbl) as blbl; destruct blbl as [blbl|]; simpl.

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

  Hypothesis (Hsimi: sim {| st_oss := getObjectStatesInit impl; st_msgs := @empty _ _ |}
                         {| st_oss := getObjectStatesInit spec; st_msgs := @empty _ _ |}).

  Theorem simulation_implies_refinement:
    Refines impl spec.
  Proof.
    unfold Simulates, Refines; intros.
    inv H.
    eapply simulation_steps in H0; [|exact Hsimi].
    destruct H0 as [? [? [? [? ?]]]].
    econstructor; eauto.
  Qed.

End Simulation.

