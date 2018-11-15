Require Import Bool List String Peano_dec.
Require Import Common FMap HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation SerialFacts.

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

  Section Facts.

    Lemma ImplStateMSI_init:
      ImplStateMSI (initsOf impl).
    Proof.
      repeat red.
      right; left.
      exists 0; repeat split;
        try (right; split; reflexivity; fail).
    Qed.

    Lemma ImplStateMSI_invStep:
      InvStep impl step_m (liftInv ImplStateMSI).
    Proof.
      apply invSeq_serializable_invStep.
      - apply ImplStateMSI_init.
      - admit. (* [InvSeq] *)
      - admit. (* [SerializableSys] *)
    Admitted.

  End Facts.
  
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

  Definition SimMsiSv: OStates ImplOStateIfc -> OStates SpecOStateIfc -> Prop :=
    fun ioss soss =>
      ImplStateI ioss \/
      (exists cv, ImplStateS cv ioss /\ SpecState cv soss) \/
      (exists cv, ImplStateM cv ioss /\ SpecState cv soss).

  Section Facts.

    Lemma SimMsiSv_init:
      SimMsiSv (initsOf impl) (initsOf spec).
    Proof.
      repeat red.
      right; left.
      exists 0; split.
      - cbn; repeat split;
          try (right; split; reflexivity; fail).
      - reflexivity.
    Qed.

    Lemma SimMsiSv_sim:
      InvSim step_m step_m (liftInv ImplStateMSI) (liftSim SimMsiSv) impl spec.
    Proof.
    Admitted.
    
    Theorem MsiSv_ok:
      (steps step_m) # (steps step_m) |-- impl ⊑ spec.
    Proof.
      apply invSim_implies_refinement
        with (ginv:= liftInv ImplStateMSI)
             (sim:= liftSim SimMsiSv).
      - apply SimMsiSv_sim.
      - apply ImplStateMSI_invStep.
      - apply SimMsiSv_init.
      - apply ImplStateMSI_init.
    Qed.

  End Facts.
  
End Sim.

