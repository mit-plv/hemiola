Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepDet SemFacts.
Require Import Simulation Serial.

Set Implicit Arguments.

Definition OInv := OState -> Prop.
Definition TInv := TState -> Prop.

Definition liftOInv (oidx: IdxT) (oinv: OInv): TInv :=
  fun tst => (tst_oss tst)@[oidx] >>=[True] (fun ost => oinv ost).

Definition tInvAnd (inv1 inv2: TInv) :=
  fun tst => inv1 tst /\ inv2 tst.
Infix "/\i" := tInvAnd (at level 80).

Definition tInvImp (inv1 inv2: TInv) :=
  forall tst, inv1 tst -> inv2 tst.
Infix "->i" := tInvImp (at level 99).

Lemma tinv_proj1: forall inv1 inv2, inv1 /\i inv2 ->i inv1.
Proof. firstorder. Qed.
Lemma tinv_proj2: forall inv1 inv2, inv1 /\i inv2 ->i inv2.
Proof. firstorder. Qed.

Section Impl.
  Variable (impl: System).

  Definition TrsInvInit (ginv: TInv) :=
    ginv (initsOf impl).

  Definition TrsInv (ginv: TInv) :=
    forall ist1,
      ginv ist1 ->
      forall ihst ist2,
        trsSteps impl ist1 ihst ist2 ->
        ginv ist2.

  Definition TrsInvIn (ginv: TInv) :=
    forall ist1,
      ginv ist1 ->
      forall imin ist2,
        step_det impl ist1 (RlblIn imin) ist2 ->
        ginv ist2.

  Definition TrsInvAtomic (ginv: TInv) :=
    forall ts rq hst mouts,
      Atomic impl ts rq hst mouts ->
      forall ist1,
        ginv ist1 ->
        forall ist2,
          steps_det impl ist1 hst ist2 ->
          ginv ist2.

End Impl.

Lemma trsInv_split:
  forall impl inv1 inv2,
    TrsInv impl inv1 ->
    TrsInv impl inv2 ->
    TrsInv impl (inv1 /\i inv2).
Proof.
  unfold TrsInv, tInvAnd; intros; dest; split; eauto.
Qed.

Ltac split_inv := apply trsInv_split.

