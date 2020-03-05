Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsInvMsg RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Require Export Ex.Mesi.MesiInvB.
Require Export Ex.Mesi.MesiInv.
Require Export Ex.Mesi.MesiInvInv0 Ex.Mesi.MesiInvInv1 Ex.Mesi.MesiInvInv2.
Require Export Ex.Mesi.MesiInvExcl.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Mesi.ImplOStateIfc.

Definition InvForSim (tr: tree) (st: State): Prop :=
  InvExcl (fst (tree2Topo tr 0)) (snd (tree2Topo tr 0)) st /\
  InvWBDir st /\ InvWBCoh st /\
  InvWB (fst (tree2Topo tr 0)) st /\
  InvNWB (fst (tree2Topo tr 0)) st /\
  MesiDownLockInv tr st.

Lemma mesi_InvForSim_ok:
  forall tr (Htr: tr <> Node nil),
    InvReachable (impl Htr) step_m (InvForSim tr).
Proof.
  intros.
  red; intros.
  red; repeat ssplit.
  - eapply mesi_InvExcl_ok; eauto.
  - eapply mesi_InvWBDir_ok; eauto.
  - eapply mesi_InvWBCoh_ok; eauto.
  - eapply mesi_InvWB_ok; eauto.
  - eapply mesi_InvNWB_ok; eauto.
  - eapply MesiDownLockInv_ok; eauto.
Qed.

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
  | [Hcoh: CohInvRq cidx ?ost _, Ho: mesiS <= _, Hfm: FirstMPI _ _ |- _] =>
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

Ltac disc_InvNWB cidx Hinv :=
  match goal with
  | [Hp: parentIdxOf _ cidx = Some _ |- _] =>
    specialize (Hinv _ _ Hp); simpl in Hinv;
    disc_rule_conds_ex
  end.

Hint Unfold InvForSim: RuleConds.

