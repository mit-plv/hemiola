Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics SemFacts.
Require Import StepSeq Simulation Serial.

Fixpoint TTransactional (tid: TrsId) (hst: History) :=
  match hst with
  | nil => True
  | tl :: hst' =>
    (match tl with
     | IlblIn _ => True
     | IlblOuts (Some hdl) _ =>
       (tmsg_tid hdl) >>=[True] (fun htid => htid = tid)
     | IlblOuts None _ => False
     end) /\ TTransactional tid hst'
  end.

Section SeqSim.

  Context {StateS LabelS: Type}
          `{HasInit StateS} `{HasLabel LabelS}.
  Variables (stepS: Step StateS LabelS)
            (sim: TState -> StateS -> Prop)
            (p: Label -> Label).

  Local Infix "≈" := sim (at level 30).

  Variables (impl spec: System).

  Definition SeqSimulates :=
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ihst ist2,
        steps step_seq impl ist1 ihst ist2 ->
        tst_tid ist2 > tst_tid ist1 ->
        TTransactional (tst_tid ist2) ihst ->
        exists sst2 shst,
          steps stepS spec sst1 shst sst2 /\
          map p (behaviorOf impl ihst) = behaviorOf spec shst.
  
  Hypothesis (Hsim: SeqSimulates).

  Lemma sequential_simulation_steps:
    forall ist1 sst1,
      ist1 ≈ sst1 ->
      forall ihst ist2,
        steps step_seq impl ist1 ihst ist2 ->
        exists sst2 shst,
          map p (behaviorOf impl ihst) = behaviorOf spec shst /\
          steps stepS spec sst1 shst sst2 /\
          ist2 ≈ sst2.
  Proof.
  Admitted.

  Hypothesis (Hsimi: sim (getStateInit impl) (getStateInit spec)).

  Theorem sequential_simulation_implies_refinement:
    step_seq # stepS |-- impl ⊑[p] spec.
  Proof.
    unfold Simulates, Refines; intros.
    inv H1.
    eapply sequential_simulation_steps in H2; [|exact Hsimi].
    destruct H2 as [sst2 [shst [? [? ?]]]].
    econstructor; eauto.
  Qed.

End SeqSim.


  
