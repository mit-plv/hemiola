Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Wf Semantics SemFacts StepDet.
Require Import Synthesis Serial SerialFacts Simulation TrsInv TrsSim.

Set Implicit Arguments.

Lemma rollbacked_enqMP_toTMsgU:
  forall (mp: Msg -> Msg) msgs emsg rb,
    enqMP (toTMsgU (mp emsg)) (deinitialize mp (rollbacked rb msgs)) =
    deinitialize mp (rollbacked rb (enqMP (toTMsgU emsg) msgs)).
Proof.
  induction msgs; simpl; intros.
  - unfold deinitialize, enqMP.
    rewrite map_app; simpl.
    reflexivity.
  - destruct (tmsg_info a); eauto.
Qed.

Lemma SimMP_ext_msg_in:
  forall (mp: Msg -> Msg) imsgs smsgs,
    SimMP mp imsgs smsgs ->
    forall emsg,
      SimMP mp (enqMP (toTMsgU emsg) imsgs)
            (enqMP (toTMsgU (mp emsg)) smsgs).
Proof.
  unfold SimMP; intros; subst.
  unfold rollback.
  apply rollbacked_enqMP_toTMsgU.
Qed.

Lemma rollbacked_app:
  forall mp1 rb mp2,
    rollbacked rb (mp1 ++ mp2) =
    rollbacked (rollbacked rb mp1) mp2.
Proof.
  induction mp1; simpl; intros; [reflexivity|].
  destruct (tmsg_info a); auto.
Qed.

Corollary trsSimulates_trsInvHolds_rules_added:
  forall impl rules spec simR ginv simP
         (Hsim1: TrsSimulates simR ginv simP impl spec)
         (Hinv1: TrsInv impl ginv)
         (Hmt1: trsPreservingSys impl)
         (Hsim2: TrsSimulates simR ginv simP (addRules rules (buildRawSys impl)) spec)
         (Hinv1: TrsInv (addRules rules (buildRawSys impl)) ginv)
         (Hmt2: trsPreservingSys (addRules rules (buildRawSys impl)))
         (Hmtdisj: TrsDisj (rulesOf impl) rules),
    TrsSimulates simR ginv simP (addRules rules impl) spec /\
    TrsInv (addRules rules impl) ginv.
Proof.
  intros.
  eapply trsSimulates_trsInvHolds_compositional
    with (impl1:= impl) (impl2:= addRules rules (buildRawSys impl)); eauto.
  unfold addRules, trsPreservingSys in *; simpl in *.
  apply Forall_app; auto.
Qed.

