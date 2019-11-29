Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepM SemFacts.

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
    forall hst ist2,
      steps stepI impl (initsOf impl) hst ist2 ->
      ginv ist2.

  Definition InvReachable :=
    forall ist,
      Reachable (steps stepI) impl ist ->
      ginv ist.
  
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
    eapply Hinvs; [| |exact H5]; auto.
    eapply reachable_steps; eauto.
  Qed.

  Lemma inv_steps: InvSteps.
  Proof.
    unfold InvSteps; intros.
    eapply inv_steps'; eauto.
    apply reachable_init.
  Qed.

  Corollary inv_reachable: InvReachable.
  Proof.
    unfold InvReachable; intros.
    destruct H2 as [ll ?].
    eapply inv_steps; eauto.
  Qed.
  
End Invariant.

Section MutualInvariant.
  Variables (SystemI StateI LabelI: Type).
  Context `{HasInit SystemI StateI} `{HasLabel LabelI}.

  Variable (impl: SystemI).

  Variables (stepI: Step SystemI StateI LabelI)
            (inv1 inv2: StateI -> Prop).

  Definition MutualInvStep1 :=
    forall ist1,
      Reachable (steps stepI) impl ist1 ->
      inv1 ist1 -> inv2 ist1 ->
      forall lbl ist2,
        stepI impl ist1 lbl ist2 ->
        inv1 ist2.

  Definition MutualInvStep2 :=
    forall ist1,
      Reachable (steps stepI) impl ist1 ->
      inv1 ist1 -> inv2 ist1 ->
      forall lbl ist2,
        stepI impl ist1 lbl ist2 ->
        inv2 ist2.

  Hypotheses (Hminvi1: InvInit impl inv1)
             (Hminvi2: InvInit impl inv2)
             (Hminvs1: MutualInvStep1)
             (Hminvs2: MutualInvStep2).

  Lemma mutual_inv_steps':
    forall ist1,
      Reachable (steps stepI) impl ist1 ->
      inv1 ist1 -> inv2 ist1 ->
      forall ihst ist2,
        steps stepI impl ist1 ihst ist2 ->
        inv1 ist2 /\ inv2 ist2.
  Proof.
    induction 4; simpl; intros; eauto.
    split.
    - eapply Hminvs1 with (ist1:= st2); eauto.
      + eapply reachable_steps; eauto.
      + apply IHsteps; auto.
      + apply IHsteps; auto.
    - eapply Hminvs2 with (ist1:= st2); eauto.
      + eapply reachable_steps; eauto.
      + apply IHsteps; auto.
      + apply IHsteps; auto.
  Qed.

  Lemma mutual_inv_steps:
    InvSteps impl stepI (fun st => inv1 st /\ inv2 st).
  Proof.
    unfold InvSteps; intros.
    eapply mutual_inv_steps'; eauto.
    apply reachable_init.
  Qed.

  Corollary mutual_inv_reachable:
    InvReachable impl stepI (fun st => inv1 st /\ inv2 st).
  Proof.
    unfold InvReachable; intros.
    destruct H2 as [ll ?].
    eapply mutual_inv_steps; eauto.
  Qed.

End MutualInvariant.

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

Infix "/\i" := invAnd (at level 80).
Infix "->i" := invImp (at level 99).

