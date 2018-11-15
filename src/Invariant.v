Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepM StepT SemFacts.

Require Import Omega.

Set Implicit Arguments.

Section Invariant.
  Variables (SystemI StateI LabelI: Type).
  Context `{HasInit SystemI StateI} `{HasLabel LabelI}.

  Variable (impl: SystemI).

  Variables (stepI: Step SystemI StateI LabelI)
            (ginv: StateI -> Prop).

  Definition Invariant := StateI -> Prop.

  Definition InvInit := ginv (initsOf impl).

  Definition InvStep :=
    forall ist1,
      Reachable (steps stepI) impl ist1 ->
      ginv ist1 ->
      forall lbl ist2,
        stepI impl ist1 lbl ist2 ->
        ginv ist2.

  Definition InvSteps :=
    forall lbl ist2,
      steps stepI impl (initsOf impl) lbl ist2 ->
      ginv ist2.

  Hypotheses (Hinvi: InvInit)
             (Hinvs: InvStep).

  Lemma inv_steps':
    forall ist1,
      Reachable (steps stepI) impl ist1 ->
      ginv ist1 ->
      forall ihst ist2,
        steps stepI impl ist1 ihst ist2 ->
        ginv ist2.
  Proof.
    induction 3; simpl; intros; eauto.

    eapply Hinvs; [| |exact H4]; auto.
    eapply reachable_steps; eauto.
  Qed.

  Lemma inv_steps: InvSteps.
  Proof.
    unfold InvSteps; intros.
    eapply inv_steps'; eauto.
    apply reachable_init.
  Qed.
  
End Invariant.

Section Operations.
  Context {StateT: Type}.

  Definition invAnd (inv1 inv2: Invariant StateT) :=
    fun tst => inv1 tst /\ inv2 tst.

  Definition invImp (inv1 inv2: Invariant StateT) :=
    forall tst, inv1 tst -> inv2 tst.

  Lemma tinv_proj1: forall inv1 inv2, invImp (invAnd inv1 inv2) inv1.
  Proof. firstorder. Qed.
  Lemma tinv_proj2: forall inv1 inv2, invImp (invAnd inv1 inv2) inv2.
  Proof. firstorder. Qed.

  Lemma inv_split:
    forall (inv1 inv2: Invariant StateT) st,
      inv1 st ->
      inv2 st ->
      (invAnd inv1 inv2) st.
  Proof.
    unfold invAnd; intros; dest; split; eauto.
  Qed.

End Operations.

Definition liftInv {oifc} (ossInv: OStates oifc -> Prop): MState oifc -> Prop :=
  fun st => ossInv (bst_oss st).

Ltac split_inv := apply inv_split.

Infix "/\i" := invAnd (at level 80).
Infix "->i" := invImp (at level 99).

