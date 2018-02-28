Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Wf Semantics SemFacts StepDet Synthesis.
Require Import Serial SerialFacts Simulation TrsInv TrsSim.

Lemma addRules_init:
  forall rules sys,
    initsOf (StateT:= TState) (addRules rules sys) =
    initsOf (StateT:= TState) sys.
Proof.
  reflexivity.
Qed.

Lemma addRules_indices:
  forall rules sys,
    indicesOf (addRules rules sys) = indicesOf sys.
Proof.
  reflexivity.
Qed.

Corollary addRules_isExternal:
  forall rules sys,
    isExternal (addRules rules sys) =
    isExternal sys.
Proof.
  unfold isExternal; intros.
  rewrite addRules_indices.
  reflexivity.
Qed.
  
Corollary addRules_isInternal:
  forall rules sys,
    isInternal (addRules rules sys) =
    isInternal sys.
Proof.
  unfold isInternal; intros.
  rewrite addRules_indices.
  reflexivity.
Qed.

Lemma buildRawSys_indicesOf:
  forall sys, indicesOf sys = indicesOf (buildRawSys sys).
Proof.
  intros; unfold indicesOf, buildRawSys; simpl.
  reflexivity.
Qed.

Corollary buildRawSys_isExternal:
  forall sys,
    isExternal (buildRawSys sys) =
    isExternal sys.
Proof.
  unfold isExternal; intros.
  rewrite <-buildRawSys_indicesOf.
  reflexivity.
Qed.

Corollary buildRawSys_isInternal:
  forall sys,
    isInternal (buildRawSys sys) =
    isInternal sys.
Proof.
  unfold isInternal; intros.
  rewrite <-buildRawSys_indicesOf.
  reflexivity.
Qed.

Lemma addRules_app:
  forall sys rules1 rules2,
    addRules (rules1 ++ rules2) sys =
    addRules rules2 (addRules rules1 sys).
Proof.
  unfold addRules; simpl; intros.
  rewrite app_assoc; reflexivity.
Qed.

Lemma addRulesSys_buildRawSys:
  forall rules sys,
    rulesOf (addRules rules (buildRawSys sys)) = rules.
Proof.
  reflexivity.
Qed.

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

