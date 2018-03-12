Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Wf Semantics SemFacts StepDet.
Require Import Synthesis Serial SerialFacts Simulation Invariant TrsSim.

Set Implicit Arguments.

Corollary trsSimulates_trsInvHolds_rules_added:
  forall impl rules spec simR ginv simP
         (Hsim1: InvStep impl step_det ginv ->
                 TrsSimulates simR ginv simP impl spec)
         (Hinv1: InvStep impl step_det ginv)
         (Hmt1: trsPreservingSys impl)
         (Hsim2: InvStep (addRules rules (buildRawSys impl)) step_det ginv ->
                 TrsSimulates simR ginv simP
                              (addRules rules (buildRawSys impl)) spec)
         (Hinv1: InvStep (addRules rules (buildRawSys impl)) step_det ginv)
         (Hmt2: trsPreservingSys (addRules rules (buildRawSys impl)))
         (Hmtdisj: TrsDisj (rulesOf impl) rules),
    TrsSimulates simR ginv simP (addRules rules impl) spec /\
    InvStep (addRules rules impl) step_det ginv.
Proof.
  intros.
  eapply trsSimulates_trsInvHolds_compositional
    with (impl1:= impl) (impl2:= addRules rules (buildRawSys impl)); eauto.
  unfold addRules, trsPreservingSys in *; simpl in *.
  apply Forall_app; auto.
Qed.

