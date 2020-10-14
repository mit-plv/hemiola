Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsInvMsg RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Msi Ex.MsiInc.Msi Ex.MsiInc.MsiTopo.

Require Export Ex.MsiInc.MsiInvB.
Require Export Ex.MsiInc.MsiInv.
Require Export Ex.MsiInc.MsiInvInv0 Ex.MsiInc.MsiInvInv1.
Require Export Ex.MsiInc.MsiInvExcl.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Msi.ImplOStateIfc.

Definition InvForSim (tr: tree) (st: State): Prop :=
  InvExcl (fst (tree2Topo tr 0)) (snd (tree2Topo tr 0)) st /\
  InvWBDir st /\ InvWBCoh st /\
  InvWB (fst (tree2Topo tr 0)) st /\
  InvDirS st /\
  MsiDownLockInv tr st.

Lemma msi_InvForSim_ok:
  forall tr (Htr: tr <> Node nil),
    InvReachable (impl Htr) step_m (InvForSim tr).
Proof.
  intros.
  red; intros.
  red; repeat ssplit.
  - eapply msi_InvExcl_ok; eauto.
  - eapply msi_InvWBDir_ok; eauto.
  - eapply msi_InvWBCoh_ok; eauto.
  - eapply msi_InvWB_ok; eauto.
  - eapply msi_InvDirS_ok; eauto.
  - eapply MsiDownLockInv_ok; eauto.
Qed.

(*! Useful tactics to be used when using the invariants *)

Ltac derive_ObjDirM oidx cidx :=
  match goal with
  | [Host: ?oss@[oidx] = Some ?ost,
           Horq: ?orqs@[oidx] = Some ?orq |- _] =>
    assert (ObjDirM orq ost cidx) by (repeat split; assumption)
  end.

Ltac derive_ObjInvRq oidx :=
  match goal with
  | [H: FirstMPI ?msgs (rqUpFrom oidx, ?rmsg) |- _] =>
    assert (ObjInvRq oidx msgs)
      by (exists (rqUpFrom oidx, rmsg); split;
                 [red; simpl; solve_in_mp|unfold sigOf; simpl; congruence])
  end.

Ltac derive_ObjInvWRq oidx :=
  match goal with
  | [H: FirstMPI ?msgs (rqUpFrom oidx, ?rmsg) |- _] =>
    assert (ObjInvWRq oidx msgs)
      by (eexists; split;
          [eapply FirstMP_InMP; eassumption
          |unfold sigOf; simpl; congruence])
  end.

Ltac disc_InvNonWB cidx Hinv :=
  repeat
    match goal with
    | [Hp: parentIdxOf _ cidx = Some _ |- _] =>
      specialize (Hinv _ _ Hp); simpl in Hinv;
      disc_rule_conds_ex
    end.

Ltac disc_InvWBCoh_inv cidx Hinv :=
  specialize (Hinv cidx); simpl in Hinv;
  disc_rule_conds_ex;
  match goal with
  | [Hcoh: CohInvRq cidx ?ost _, Ho: msiS <= _, Hfm: FirstMPI _ _ |- _] =>
    specialize (Hcoh _ (FirstMP_InMP Hfm));
    unfold sigOf in Hcoh; simpl in Hcoh;
    specialize (Hcoh ltac:(congruence));
    specialize (Hcoh Ho)
  end.

Ltac disc_InvWB cidx Hinv :=
  match goal with
  | [Hp: parentIdxOf _ cidx = Some _ |- _] =>
    specialize (Hinv _ _ Hp); simpl in Hinv;
    disc_rule_conds_ex
  end.

Hint Unfold InvForSim: RuleConds.

