Require Import Bool List String Peano_dec Lia.
Require Import Common FMap HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsCorrect.

Require Import Msi MsiSv SpecSv MsiSvTopo MsiSvInv.

Set Implicit Arguments.

Import MonadNotations.
Import CaseNotations.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Section Sim.

  Local Definition spec := SpecSv.spec 1.
  Local Definition impl := MsiSv.impl.

  (** Simulation between states *)

  Definition SpecState (v: nat) (oss: OStates SpecOStateIfc): Prop :=
    sost <-- oss@[specIdx]; sost#[specValueIdx] = v.

  Definition SimState (ioss: OStates ImplOStateIfc) (iorqs: ORqs Msg)
             (soss: OStates SpecOStateIfc): Prop :=
    post <-- ioss@[parentIdx];
      cost1 <-- ioss@[child1Idx];
      cost2 <-- ioss@[child2Idx];
      porq <-- iorqs@[parentIdx];
      corq1 <-- iorqs@[child1Idx];
      corq2 <-- iorqs@[child2Idx];
      (exists cv,
          ImplStateCoh post cost1 cost2 porq corq1 corq2 cv /\
          SpecState cv soss).

  Definition SimMP (imsgs: MessagePool Msg) (iorqs: ORqs Msg)
             (smsgs: MessagePool Msg) :=
    corq1 <-- iorqs@[child1Idx];
      corq2 <-- iorqs@[child2Idx];
      (corq1@[upRq] >>= (fun rqiu1 => Some rqiu1.(rqi_msg)))
        ::> (findQ ec1 imsgs) = findQ (erq 0) smsgs /\
      (corq2@[upRq] >>= (fun rqiu2 => Some rqiu2.(rqi_msg)))
        ::> (findQ ec2 imsgs) = findQ (erq 1) smsgs /\
      findQ ce1 imsgs = findQ (ers 0) smsgs /\
      findQ ce2 imsgs = findQ (ers 1) smsgs.
  
  Definition SimMSI (ist: MState ImplOStateIfc) (sst: MState SpecOStateIfc): Prop :=
    SimState ist.(bst_oss) ist.(bst_orqs) sst.(bst_oss) /\
    SimMP ist.(bst_msgs) ist.(bst_orqs) sst.(bst_msgs).

  Section Facts.

    Lemma SimMsiSv_init:
      SimMSI (initsOf impl) (initsOf spec).
    Proof.
      vm_compute.
      split.
      - exists 0; split.
        + firstorder.
        + reflexivity.
      - repeat split.
    Qed.

    Lemma SimMsiSv_sim:
      InvSim step_m step_m ImplStateInv SimMSI impl spec.
    Proof.
      red; intros.
      inv H2; [simpl; eauto|..].

      - destruct sst1 as [soss1 sorqs1 smsgs1]; simpl in *.
        destruct H0; simpl in *.
        do 2 eexists.
        repeat split; simpl.
        + eapply SmIns; eauto.
        + reflexivity.
        + assumption.
        + simpl.
        
    Admitted.
    
    Theorem MsiSv_ok:
      (steps step_m) # (steps step_m) |-- impl ⊑ spec.
    Proof.
      apply invSim_implies_refinement
        with (ginv:= ImplStateInv)
             (sim:= SimMSI).
      - apply SimMsiSv_sim.
      - apply ImplStateInv_invStep.
      - apply SimMsiSv_init.
      - apply ImplStateInv_init.
    Qed.

  End Facts.
  
End Sim.

