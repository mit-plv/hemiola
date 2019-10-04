Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsInvMsg RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Require Export Ex.Mesi.MesiInvB.
Require Export Ex.Mesi.MesiInv Ex.Mesi.MesiInvInv0 Ex.Mesi.MesiInvInv1.
Require Export Ex.Mesi.MesiInvExcl.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Mesi.ImplOStateIfc.

Definition InvForSim (topo: DTree) (st: MState): Prop :=
  InvExcl st /\
  InvWBDir st /\ InvWBCoh st /\ InvWB topo st /\
  MesiDownLockInv topo st.

Lemma mesi_InvForSim_init:
  forall tr (Htr: tr <> Node nil),
    InvForSim (fst (tree2Topo tr 0)) (initsOf (impl Htr)).
Proof.
Admitted.

Lemma mesi_InvForSim_ok:
  forall tr (Htr: tr <> Node nil),
    InvStep (impl Htr) step_m (InvForSim (fst (tree2Topo tr 0))).
Proof.
Admitted.

(*! Useful tactics to be used when using the invariants *)

Ltac derive_ObjDirE oidx cidx :=
  match goal with
  | [Host: ?oss@[oidx] = Some ?ost,
           Horq: ?orqs@[oidx] = Some ?orq |- _] =>
    assert (ObjDirE orq ost cidx) by (repeat split; assumption)
  end.

Ltac derive_ObjDirME oidx cidx :=
  match goal with
  | [Host: ?oss@[oidx] = Some ?ost,
           Horq: ?orqs@[oidx] = Some ?orq |- _] =>
    assert (ObjDirME orq ost cidx) by (repeat split; assumption)
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
  | [Hcoh: CohInvRq cidx ?ost _, Ho: ObjOwned ?ost, Hfm: FirstMPI _ _ |- _] =>
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

