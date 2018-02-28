Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepDet SemFacts.
Require Import Simulation Serial.

Set Implicit Arguments.

Definition OInv := OState -> Prop.
Definition Inv := TState -> Prop.

Definition liftOInv (oidx: IdxT) (oinv: OInv): Inv :=
  fun tst => (tst_oss tst)@[oidx] >>=[True] (fun ost => oinv ost).

Definition invAnd (inv1 inv2: Inv) :=
  fun tst => inv1 tst /\ inv2 tst.
Infix "/\i" := invAnd (at level 80).

Definition invImp (inv1 inv2: Inv) :=
  forall tst, inv1 tst -> inv2 tst.
Infix "->i" := invImp (at level 99).

Lemma inv_proj1: forall inv1 inv2, inv1 /\i inv2 ->i inv1.
Proof. firstorder. Qed.
Lemma inv_proj2: forall inv1 inv2, inv1 /\i inv2 ->i inv2.
Proof. firstorder. Qed.

Definition AInv := TrsId -> Msg -> THistory -> MessagePool TMsg -> TState -> Prop.
Definition ainvAnd (ainv1 ainv2: AInv) :=
  fun ts rq hst mouts tst =>
    ainv1 ts rq hst mouts tst /\ ainv2 ts rq hst mouts tst.
Infix "/\a" := ainvAnd (at level 80).
Definition ainvImp (ainv1 ainv2: AInv) :=
  forall ts rq hst mouts tst,
    ainv1 ts rq hst mouts tst -> ainv2 ts rq hst mouts tst.
Infix "->a" := ainvImp (at level 99).

Lemma ainv_proj1: forall ainv1 ainv2, ainv1 /\a ainv2 ->a ainv1.
Proof. firstorder. Qed.
Lemma ainv_proj2: forall ainv1 ainv2, ainv1 /\a ainv2 ->a ainv2.
Proof. firstorder. Qed.

Section Impl.
  Variable (impl: System).

  Definition TrsInvInit (ginv: Inv) :=
    ginv (initsOf impl).

  Definition TrsInv (ginv: Inv) :=
    forall ist1,
      ginv ist1 ->
      forall ihst ist2,
        trsSteps impl ist1 ihst ist2 ->
        ginv ist2.

  Definition TrsInvIn (ginv: Inv) :=
    forall ist1,
      ginv ist1 ->
      forall imin ist2,
        step_det impl ist1 (IlblIn imin) ist2 ->
        ginv ist2.

  Definition TrsInvAtomic (ginv: Inv) :=
    forall ts rq hst mouts,
      Atomic impl ts rq hst mouts ->
      forall ist1,
        ginv ist1 ->
        forall ist2,
          steps_det impl ist1 hst ist2 ->
          ginv ist2.

  Definition TrsAInv (ginv: Inv) (ainv: AInv) :=
    forall ts rq hst mouts,
      Atomic impl ts rq hst mouts ->
      forall ist1 ist2,
        steps_det impl ist1 hst ist2 ->
        ginv ist1 ->
        ainv ts rq hst mouts ist2.

End Impl.

Lemma trsInv_split:
  forall impl inv1 inv2,
    TrsInv impl inv1 ->
    TrsInv impl inv2 ->
    TrsInv impl (inv1 /\i inv2).
Proof.
  unfold TrsInv, invAnd; intros; dest; split; eauto.
Qed.

Ltac split_inv := apply trsInv_split.

Lemma trsAInv_split:
  forall impl ginv ainv1 ainv2,
    TrsAInv impl ginv ainv1 ->
    TrsAInv impl ginv ainv2 ->
    TrsAInv impl ginv (ainv1 /\a ainv2).
Proof.
  intros; split; eauto.
Qed.

Ltac split_ainv := apply trsAInv_split.

Lemma trsAInv_ginv_weaken:
  forall impl ginv1 ainv,
    TrsAInv impl ginv1 ainv ->
    forall ginv2,
      ginv2 ->i ginv1 ->
      TrsAInv impl ginv2 ainv.
Proof.
  unfold TrsAInv; intros; eauto.
Qed.

