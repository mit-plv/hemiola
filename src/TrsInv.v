Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepDet SemFacts.
Require Import Simulation Serial.

Set Implicit Arguments.

Section Impl.
  Variable (impl: System).

  Definition TrsInvInit (ginv: TState -> Prop) :=
    ginv (getStateInit impl).

  Definition TrsInv (ginv: TState -> Prop) :=
    forall ist1,
      ginv ist1 ->
      forall ihst ist2,
        trsSteps impl ist1 ihst ist2 ->
        ginv ist2.

  Definition TrsInvIn (ginv: TState -> Prop) :=
    forall ist1,
      ginv ist1 ->
      forall imin ist2,
        step_det impl ist1 (IlblIn imin) ist2 ->
        ginv ist2.

  Definition TrsInvAtomic (ginv: TState -> Prop) :=
    forall ti hst mouts orsout,
      Atomic impl ti hst mouts orsout ->
      forall ist1,
        ginv ist1 ->
        forall ist2,
          steps_det impl ist1 hst ist2 ->
          ginv ist2.

  Definition TrsAInvInit
             (ainv: TInfo -> History -> MessagePool TMsg -> TState -> Prop) :=
    forall ti tst, ainv ti nil (enqMP (toTMsgU (tinfo_rqin ti)) nil) tst.

  Definition TrsAInv (ginv: TState -> Prop)
             (ainv: TInfo -> History -> MessagePool TMsg -> TState -> Prop) :=
    forall ti hst mouts orsout,
      Atomic impl ti hst mouts orsout ->
      forall ist1 ist2,
        steps_det impl ist1 hst ist2 ->
        ginv ist1 ->
        ainv ti hst mouts ist2.

End Impl.

