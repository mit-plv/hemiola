Require Import Bool List String PeanoNat.
Require Import Common FMap ListSupport Syntax Semantics StepM SemFacts.
Require Import Lia.

Import PropMonadNotations.

Local Open Scope fmap.

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

Section ObjInvariant.
  Context `{DecValue} `{OStateIfc}.

  Variable oidx: IdxT.

  Definition ObjReachable (sys: System) (ost: OState) (orq: ORq Msg): Prop :=
    exists st,
      (st_oss st)@[oidx] = Some ost /\
      (st_orqs st)@[oidx] = Some orq /\
      Reachable (steps step_m) sys st.

  Definition ObjInv := OState -> ORq Msg -> Prop.

  Variable (impl: System).
  Variables (oinv: ObjInv).

  Definition liftObjInv (st: State) :=
    osti <+- (st_oss st)@[oidx];
      orqi <+- (st_orqs st)@[oidx];
      oinv osti orqi.

  Definition ObjInvInit :=
    liftObjInv (initsOf impl).

  Definition ObjInvStep :=
    forall ist1,
      Reachable (steps step_m) impl ist1 ->
      forall ost orq,
        (st_oss ist1)@[oidx] = Some ost ->
        (st_orqs ist1)@[oidx] = Some orq ->
        oinv ost orq ->
        forall ridx mins mouts ist2,
          step_m impl ist1 (RlblInt oidx ridx mins mouts) ist2 ->
          liftObjInv ist2.

  Definition ObjInvSteps :=
    forall hst ist2,
      steps step_m impl (initsOf impl) hst ist2 ->
      liftObjInv ist2.

  Definition ObjInvReachable :=
    forall ost orq,
      ObjReachable impl ost orq -> oinv ost orq.

  Hypotheses (Hoinvi: ObjInvInit)
             (Hoinvs: ObjInvStep).

  Lemma obj_inv_steps':
    forall ist1,
      Reachable (steps step_m) impl ist1 ->
      (forall ost orq,
          (st_oss ist1)@[oidx] = Some ost ->
          (st_orqs ist1)@[oidx] = Some orq ->
          oinv ost orq) ->
      forall ihst ist2,
        steps step_m impl ist1 ihst ist2 ->
        liftObjInv ist2.
  Proof.
    induction 3; simpl; intros.
    - red.
      destruct (st_oss st)@[oidx] as [ost|]; [|simpl; auto].
      destruct (st_orqs st)@[oidx] as [orq|]; [|simpl; auto].
      simpl; auto.

    - specialize (IHsteps H1 H2).
      pose proof H4 as Hstep.
      inv H4; auto.
      destruct (idx_dec oidx (obj_idx obj));
        [|red; simpl; mred].

      red in IHsteps; simpl in IHsteps.
      rewrite e in IHsteps; rewrite H8, H9 in IHsteps; simpl in IHsteps.

      eapply Hoinvs; [..|rewrite e; eassumption].
      + eapply reachable_steps; eauto.
      + simpl; rewrite e; eassumption.
      + simpl; rewrite e; eassumption.
      + assumption.
  Qed.

  Lemma obj_inv_steps: ObjInvSteps.
  Proof.
    unfold ObjInvSteps; intros.
    eapply obj_inv_steps'; [..|eassumption].
    - apply reachable_init.
    - intros.
      do 2 red in Hoinvi.
      rewrite H2, H3 in Hoinvi; auto.
  Qed.

  Corollary obj_inv_reachable: ObjInvReachable.
  Proof.
    unfold ObjInvReachable; intros.
    destruct H1 as [st ?]; dest.
    destruct H3 as [ll ?].
    apply obj_inv_steps in H3; red in H3.
    rewrite H1, H2 in H3; auto.
  Qed.

End ObjInvariant.

Definition liftObjInvs `{DecValue} `{OStateIfc} (oinvs: IdxT -> ObjInv): State -> Prop :=
  fun st => forall oidx, liftObjInv oidx (oinvs oidx) st.
