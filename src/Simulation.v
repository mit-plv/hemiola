Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics SemFacts.

Section Simulation.
  Context {SysI SysS StateI LabelI StateS LabelS: Type}
          `{IsSystem SysI StateI} `{HasLabel LabelI}
          `{IsSystem SysS StateS} `{HasLabel LabelS}.
  Variables (stepI: Step SysI StateI LabelI) (stepS: Step SysS StateS LabelS)
            (sim: StateI -> StateS -> Prop)
            (p: Label -> Label).

  Local Infix "≈" := sim (at level 30).

  Variables (impl: SysI) (spec: SysS).

  Definition Simulates :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ilbl ist2,
        stepI impl ist1 ilbl ist2 ->
        match extLabel (StateT:= StateI) impl (getLabel ilbl) with
        | None =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              extLabel (StateT:= StateS) spec (getLabel slbl) = None /\
              ist2 ≈ sst2) \/
          ist2 ≈ sst1
        | Some elbl =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              extLabel (StateT:= StateS) spec (getLabel slbl) = Some (p elbl) /\
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
          map p (behaviorOf (StateT:= StateI) impl ihst) =
          behaviorOf (StateT:= StateS) spec shst /\
          ist2 ≈ sst2.
  Proof.
    induction 2; simpl; intros;
      [exists sst1, nil; repeat split; auto; constructor|].

    specialize (IHsteps H3).
    destruct IHsteps as [sst2 [shst [? [? ?]]]].

    eapply Hsim in H5; [|exact H8].
    remember (extLabel impl (getLabel lbl)) as ilbl; clear Heqilbl.
    destruct ilbl as [elbl|].

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
    (steps stepI) # (steps stepS) |-- impl ⊑[p] spec.
  Proof.
    unfold Simulates, Refines; intros.
    inv H3.
    eapply simulation_steps in H4; [|exact Hsimi].
    destruct H4 as [sst2 [shst [? [? ?]]]].
    econstructor; eauto.
  Qed.

End Simulation.

Section LInvSim.
  Context {SysI SysS StateI LabelI StateS LabelS: Type}
          `{IsSystem SysI StateI} `{HasLabel LabelI}
          `{IsSystem SysS StateS} `{HasLabel LabelS}.
  Variables (stepI: Step SysI StateI LabelI) (stepS: Step SysS StateS LabelS)
            (sim: StateI -> StateS -> Prop)
            (p: Label -> Label)
            (linv: LabelI -> Prop).

  Local Infix "≈" := sim (at level 30).

  Variables (impl: SysI) (spec: SysS).

  Definition LInvSim :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ilbl ist2,
        linv ilbl ->
        stepI impl ist1 ilbl ist2 ->
        match extLabel (StateT:= StateI) impl (getLabel ilbl) with
        | None =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              extLabel (StateT:= StateS) spec (getLabel slbl) = None /\
              ist2 ≈ sst2) \/
          ist2 ≈ sst1
        | Some elbl =>
          (exists sst2 slbl,
              stepS spec sst1 slbl sst2 /\
              extLabel (StateT:= StateS) spec (getLabel slbl) = Some (p elbl) /\
              ist2 ≈ sst2)
        end.

  Hypothesis (Hsim: LInvSim).

  Lemma label_inv_simulation_steps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ihst ist2,
        Forall linv ihst ->
        steps stepI impl ist1 ihst ist2 ->
        exists sst2 shst,
          steps stepS spec sst1 shst sst2 /\
          map p (behaviorOf (StateT:= StateI) impl ihst) =
          behaviorOf (StateT:= StateS) spec shst /\
          ist2 ≈ sst2.
  Proof.
    induction 3; simpl; intros;
      [exists sst1, nil; repeat split; auto; constructor|].

    inv H4.
    specialize (IHsteps H3 H10).
    destruct IHsteps as [sst2 [shst [? [? ?]]]].

    eapply Hsim in H6; [|exact H8|exact H9].
    remember (extLabel impl (getLabel lbl)) as ilbl; clear Heqilbl.
    destruct ilbl as [elbl|].

    - destruct H6 as [sst3 [slbl [? [? ?]]]].
      eexists; eexists (_ :: _); repeat split; eauto.
      + econstructor; eauto.
      + simpl; erewrite H7, H11; simpl.
        reflexivity.
    - destruct H6.
      * destruct H6 as [sst3 [slbl [? [? ?]]]].
        eexists; eexists (slbl :: _); repeat split; eauto.
        -- econstructor; eauto.
        -- simpl; rewrite H7, H11; simpl; reflexivity.
      * exists sst2, shst; repeat split; auto.
  Qed.

End LInvSim.

Section SimMap.
  Variable (mmap: Msg -> Msg).

  Definition LabelMap (il: Label) :=
    match il with
    | LblIn imsg => LblIn (mmap imsg)
    | LblOuts outs => LblOuts (map mmap outs)
    end.

  Definition ValidMsgMap (impl spec: System) :=
    forall msg,
      isInternal impl (mid_from (msg_id msg)) =
      isInternal spec (mid_from (msg_id (mmap msg))) /\
      isInternal impl (mid_to (msg_id msg)) =
      isInternal spec (mid_to (msg_id (mmap msg))).

  Lemma validMsgMap_from_isExternal:
    forall impl spec,
      ValidMsgMap impl spec ->
      forall msg b,
        isExternal impl (mid_from (msg_id msg)) = b ->
        isExternal spec (mid_from (msg_id (mmap msg))) = b.
  Proof.
    unfold ValidMsgMap; intros.
    rewrite <-H0.
    specialize (H msg); dest.
    do 2 rewrite internal_external_negb in H.
    destruct (isExternal _ _);
      destruct (isExternal _ _); auto.
  Qed.

  Lemma validMsgMap_to_isInternal:
    forall impl spec,
      ValidMsgMap impl spec ->
      forall msg b,
        isInternal impl (mid_to (msg_id msg)) = b ->
        isInternal spec (mid_to (msg_id (mmap msg))) = b.
  Proof.
    unfold ValidMsgMap; intros.
    rewrite <-H0.
    specialize (H msg); dest; auto.
  Qed.

  Lemma validMsgMap_same_indices:
    forall impl1 spec,
      ValidMsgMap impl1 spec ->
      forall impl2,
        indicesOf impl1 = indicesOf impl2 ->
        ValidMsgMap impl2 spec.
  Proof.
    unfold ValidMsgMap, isExternal, isInternal; intros.
    rewrite <-H0; auto.
  Qed.
  
End SimMap.
  
Definition LiftSimL {StateI1 StateS} (sim: StateI1 -> StateS -> Prop)
           {StateI2} (f: StateI2 -> StateI1): StateI2 -> StateS -> Prop :=
  fun sti2 sts => sim (f sti2) sts.

Definition LiftSimR {StateI StateS1} (sim: StateI -> StateS1 -> Prop)
           {StateS2} (f: StateS2 -> StateS1): StateI -> StateS2 -> Prop :=
  fun sti sts2 => sim sti (f sts2).

