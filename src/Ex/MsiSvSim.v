Require Import Bool List String Peano_dec.
Require Import Common FMap HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant Simulation SerialFacts.

Require Import Msi MsiSv SpecSv.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Section Inv.

  Definition ImplOStateI (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] = msiI.

  Definition ImplOStateS (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] = msiI \/
    (ost#[implStatusIdx] = msiS /\ ost#[implValueIdx] = cv).

  Definition ImplOStateM (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] = msiM /\ ost#[implValueIdx] = cv.

  Definition ImplStateI (oss: OStates ImplOStateIfc): Prop.
  Proof.
    refine ((oss@[parentIdx]) >>=[False] (fun post => _)).
    refine ((oss@[child1Idx]) >>=[False] (fun cost1 => _)).
    refine ((oss@[child2Idx]) >>=[False] (fun cost2 => _)).
    exact (ImplOStateI post /\ (* Directory status is I as well. *)
           ImplOStateI cost1 /\ ImplOStateI cost2).
  Defined.

  Definition ImplStateS (cv: nat) (oss: OStates ImplOStateIfc): Prop.
  Proof.
    refine ((oss@[parentIdx]) >>=[False] (fun post => _)).
    refine ((oss@[child1Idx]) >>=[False] (fun cost1 => _)).
    refine ((oss@[child2Idx]) >>=[False] (fun cost2 => _)).
    refine (post#[implStatusIdx] = msiS /\ _). (* Directory status is S. *)
    exact (ImplOStateS cv cost1 /\ ImplOStateS cv cost2).
  Defined.

  Definition ImplStateM (cv: nat) (oss: OStates ImplOStateIfc): Prop.
  Proof.
    refine ((oss@[parentIdx]) >>=[False] (fun post => _)).
    refine ((oss@[child1Idx]) >>=[False] (fun cost1 => _)).
    refine ((oss@[child2Idx]) >>=[False] (fun cost2 => _)).
    refine (post#[implStatusIdx] = msiM /\ _). (* Directory status is M. *)
    exact ((ImplOStateM cv cost1 /\ ImplOStateI cost2) \/
           (ImplOStateI cost1 /\ ImplOStateM cv cost2)).
  Defined.

  Definition ImplStateMSI (oss: OStates ImplOStateIfc): Prop :=
    ImplStateI oss \/
    (exists cv, ImplStateS cv oss) \/
    (exists cv, ImplStateM cv oss).
  
End Inv.

Section Sim.

  Local Definition spec := SpecSv.spec 1.
  Local Definition impl := MsiSv.impl.

  (** Simulation between [MState]s *)

  Definition SpecState (v: nat) (oss: OStates SpecOStateIfc): Prop.
  Proof.
    refine ((oss@[specIdx]) >>=[False] (fun sost => _)).
    exact (sost#[specValueIdx] = v).
  Defined.

  Definition SimOStates: OStates ImplOStateIfc -> OStates SpecOStateIfc -> Prop :=
    fun ioss soss =>
      ImplStateI ioss \/
      (exists cv, ImplStateS cv ioss /\ SpecState cv soss) \/
      (exists cv, ImplStateM cv ioss /\ SpecState cv soss).

  Definition SimMsiSv: MState ImplOStateIfc -> MState SpecOStateIfc -> Prop :=
    fun ist sst => SimOStates (bst_oss ist) (bst_oss sst).

  Section Facts.

    Lemma SimMsiSv_init:
      SimMsiSv (initsOf impl) (initsOf spec).
    Proof.
      repeat red.
      right; left.
      exists 0; split.
    Admitted.

  End Facts.
  
End Sim.

