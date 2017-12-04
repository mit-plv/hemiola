Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet SemFacts.
Require Import Simulation Serial.

Require Import Omega.

Set Implicit Arguments.

Section TrsSim.
  Variables (sim: TState -> TState -> Prop)
            (p: Label -> Label).

  Local Infix "≈" := sim (at level 30).

  Variables (impl spec: System).

  Definition TrsSimulates :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ihst ist2,
        trsSteps impl ist1 ihst ist2 ->
        exists sst2 shst,
          map p (behaviorOf impl ihst) = behaviorOf spec shst /\
          steps_det spec sst1 shst sst2 /\
          ist2 ≈ sst2.

  Hypothesis (Hsim: TrsSimulates).

  Lemma trs_simulation_steps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall trss ihst ist2,
        Forall (Transactional impl) trss ->
        ihst = concat trss ->
        steps_det impl ist1 ihst ist2 ->
        exists sst2 shst,
          map p (behaviorOf impl ihst) = behaviorOf spec shst /\
          steps_det spec sst1 shst sst2 /\
          ist2 ≈ sst2.
  Proof.
    induction trss as [|trs trss]; simpl; intros; subst.
    - inv H2; exists sst1, nil; repeat split.
      + constructor.
      + assumption.
    - inv H0.
      eapply steps_split in H2; [|reflexivity].
      destruct H2 as [sti [? ?]].
      specialize (IHtrss _ _ H5 eq_refl H0).
      destruct IHtrss as [isst [ishst [? [? ?]]]].
      pose proof (Hsim H6 (conj H1 H4)).
      destruct H7 as [sst2 [shst [? [? ?]]]].
      do 2 eexists; repeat split.
      + instantiate (1:= _ ++ _).
        do 2 rewrite behaviorOf_app.
        rewrite map_app.
        rewrite H2, H7; reflexivity.
      + eapply steps_append; eauto.
      + assumption.
  Qed.

  Corollary simulation_seqSteps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ihst ist2,
        seqSteps impl ist1 ihst ist2 ->
        exists sst2 shst,
          map p (behaviorOf impl ihst) = behaviorOf spec shst /\
          steps_det spec sst1 shst sst2 /\
          ist2 ≈ sst2.
  Proof.
    unfold seqSteps, Sequential; intros; dest; subst.
    eapply trs_simulation_steps; eauto.
  Qed.

  Hypothesis (Hsimi: sim (getStateInit impl) (getStateInit spec)).

  Theorem sequential_simulation_implies_refinement:
    seqSteps # steps_det |-- impl ⊑[p] spec.
  Proof.
    unfold Simulates, Refines; intros.
    inv H.
    eapply simulation_seqSteps in H0; [|exact Hsimi].
    destruct H0 as [sst2 [shst [? [? ?]]]].
    econstructor; eauto.
  Qed.

End TrsSim.
  
