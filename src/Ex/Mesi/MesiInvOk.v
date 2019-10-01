Require Import Bool List String Peano_dec Lia.
Require Import Common FMap IndexSupport HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsLang RqRsInvMsg RqRsCorrect.

Require Import Ex.Spec Ex.SpecInds Ex.Template.
Require Import Ex.Mesi Ex.Mesi.Mesi Ex.Mesi.MesiTopo.

Require Export Ex.Mesi.MesiInvB.
Require Export Ex.Mesi.MesiInv Ex.Mesi.MesiInvInv0 Ex.Mesi.MesiInvInv1.

Set Implicit Arguments.

Import PropMonadNotations.
Import CaseNotations.

Local Open Scope list.
Local Open Scope hvec.
Local Open Scope fmap.

Existing Instance Mesi.ImplOStateIfc.

(** TODO: make a new file (maybe [MesiInvExcl.v]), move below definitions,
 * and prove them in that file. *)
Definition InvObjExcl0 (oidx: IdxT) (ost: OState) (msgs: MessagePool Msg) :=
  ObjExcl0 oidx ost msgs -> NoCohMsgs oidx msgs.

Definition InvExcl (st: MState): Prop :=
  forall eidx,
    eost <+- (bst_oss st)@[eidx];
      (InvObjExcl0 eidx eost (bst_msgs st) /\
       (ObjExcl eidx eost (bst_msgs st) ->
        forall oidx,
          oidx <> eidx ->
          ost <+- (bst_oss st)@[oidx];
            ObjInvalid oidx ost (bst_msgs st))).
(** -- end of the exclusiveness invariants *)

Definition InvForSim (topo: DTree) (st: MState): Prop :=
  InvExcl st /\
  InvWBCoh st /\ InvWB topo st /\
  MesiDownLockInv topo st.

Section Facts.

  Lemma InvExcl_excl_invalid:
    forall st (He: InvExcl st) msgs eidx eost,
      bst_msgs st = msgs ->
      (bst_oss st)@[eidx] = Some eost ->
      NoRsI eidx msgs ->
      mesiE <= eost#[status] ->
      forall oidx ost,
        oidx <> eidx ->
        (bst_oss st)@[oidx] = Some ost ->
        ObjInvalid oidx ost msgs.
  Proof.
    intros; subst.
    specialize (He eidx).
    disc_rule_conds_ex.
    unfold ObjExcl, ObjExcl0 in H5; simpl in H5.
    specialize (H5 (or_introl (conj H2 H1)) _ H3).
    solve_rule_conds_ex.
  Qed.

  Corollary InvExcl_excl_invalid_status:
    forall st (He: InvExcl st) eidx eost,
      (bst_oss st)@[eidx] = Some eost ->
      NoRsI eidx (bst_msgs st) ->
      mesiE <= eost#[status] ->
      forall oidx ost,
        oidx <> eidx ->
        (bst_oss st)@[oidx] = Some ost ->
        NoRsI oidx (bst_msgs st) ->
        ost#[status] = mesiI.
  Proof.
    intros.
    eapply InvExcl_excl_invalid in H1; eauto.
    destruct H1.
    - apply H1.
    - exfalso; eapply NoRsI_MsgExistsSig_InvRs_false; eauto.
  Qed.
  
End Facts.

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

