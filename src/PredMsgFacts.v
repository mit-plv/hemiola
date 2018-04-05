Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics SemFacts StepT.
Require Import Invariant Simulation.
Require Import Serial SerialFacts.
Require Import PredMsg StepPred.

Set Implicit Arguments.

Section GivenMsg.
  Variable (MsgT SysT: Type).
  Context `{HasMsg MsgT} `{IsSystem SysT}.

  Lemma buildRawPSys_indicesOf:
    forall (sys: SysT), indicesOf sys = indicesOf (buildRawPSys MsgT sys).
  Proof.
    reflexivity.
  Qed.

  Corollary buildRawPSys_isExternal:
    forall (sys: SysT), isExternal (buildRawPSys MsgT sys) = isExternal sys.
  Proof.
    unfold isExternal; intros.
    rewrite <-buildRawPSys_indicesOf.
    reflexivity.
  Qed.

  Corollary buildRawPSys_isInternal:
    forall (sys: SysT), isInternal (buildRawPSys MsgT sys) = isInternal sys.
  Proof.
    unfold isInternal; intros.
    rewrite <-buildRawPSys_indicesOf.
    reflexivity.
  Qed.

  Lemma buildRawPSys_pToSystem_buildRawSys:
    forall (sys: SysT), pToSystem (buildRawPSys MsgT sys) = buildRawSys sys.
  Proof.
    reflexivity.
  Qed.

  Lemma addPRules_indices:
    forall rules sys,
      indicesOf (addPRules (MsgT:= MsgT) rules sys) =
      indicesOf sys.
  Proof.
    reflexivity.
  Qed.

  Corollary addPRules_isExternal:
    forall rules sys,
      isExternal (addPRules (MsgT:= MsgT) rules sys) =
      isExternal sys.
  Proof.
    unfold isExternal; intros.
    rewrite addPRules_indices.
    reflexivity.
  Qed.

  Corollary addPRules_isInternal:
    forall rules sys,
      isInternal (addPRules (MsgT:= MsgT) rules sys) =
      isInternal sys.
  Proof.
    unfold isInternal; intros.
    rewrite addPRules_indices.
    reflexivity.
  Qed.

  Corollary addPRules_behaviorOf:
    forall psys prules phst,
      behaviorOf (addPRules (MsgT:= MsgT) prules psys) phst =
      behaviorOf psys phst.
  Proof.
    induction phst; [reflexivity|].
    simpl; rewrite IHphst; reflexivity.
  Qed.

  Lemma pToSystem_indices:
    forall psys, indicesOf psys = indicesOf (pToSystem (MsgT:= MsgT) psys).
  Proof.
    reflexivity.
  Qed.

  Corollary pToSystem_isExternal:
    forall psys idx,
      isExternal psys idx = isExternal (pToSystem (MsgT:= MsgT) psys) idx.
  Proof.
    unfold isExternal; intros.
    rewrite pToSystem_indices; reflexivity.
  Qed.

  Corollary pToSystem_isInternal:
    forall psys idx,
      isInternal psys idx = isInternal (pToSystem (MsgT:= MsgT) psys) idx.
  Proof.
    unfold isInternal; intros.
    rewrite pToSystem_indices; reflexivity.
  Qed.

  Lemma pmsg_omsg_extOuts:
    forall psys msgs,
      extOuts psys (map (fun pmsg => tmsg_msg (pmsg_omsg pmsg)) msgs) =
      extOuts (pToSystem (MsgT:= MsgT) psys)
              (map tmsg_msg (map (@pmsg_omsg _) msgs)).
  Proof.
    induction msgs; simpl; intros; [reflexivity|].
    unfold toExternal.
    rewrite pToSystem_isExternal, IHmsgs.
    reflexivity.
  Qed.

  Lemma pToLabel_extLabel:
    forall psys l,
      extLabel psys (pToLabel l) =
      extLabel (pToSystem (MsgT:= MsgT) psys) (iToLabel (pToTLabel l)).
  Proof.
    unfold extLabel; simpl; intros.
    destruct l; cbn.
    - reflexivity.
    - rewrite <-pmsg_omsg_extOuts; reflexivity.
  Qed.

  Lemma pToTHistory_behaviorOf:
    forall psys phst,
      behaviorOf psys phst =
      behaviorOf (pToSystem (MsgT:= MsgT) psys) (pToTHistory phst).
  Proof.
    induction phst; simpl; intros; [reflexivity|].
    rewrite IHphst, <-pToLabel_extLabel; reflexivity.
  Qed.

End GivenMsg.

Lemma pmsg_omsg_FirstMP:
  forall mp msg,
    FirstMP mp msg ->
    FirstMP (map (@pmsg_omsg _) mp) (pmsg_omsg msg).
Proof.
  intros; eapply mmap_FirstMP; eauto.
Qed.

Lemma atomic_history_pred_tinfo:
  forall sys ts rq hst mouts,
    Atomic sys ts rq hst mouts ->
    forall st1 st2,
      steps step_t sys st1 hst st2 ->
      forall phst,
        pToTHistory phst = hst ->
        Forall
          (fun lbl =>
             match lbl with
             | PlblIn _ => False
             | PlblOuts _ pins pouts =>
               Forall (fun pmsg =>
                         let tmsg := pmsg_omsg pmsg in
                         let msg := tmsg_msg tmsg in
                         if fromExternal sys msg then
                           msg = rq /\ tmsg_info tmsg = None
                         else
                           tmsg_info tmsg = Some (buildTInfo ts [rq])
                      ) pins /\
               Forall (fun pmsg =>
                         tmsg_info (pmsg_omsg pmsg) = Some (buildTInfo ts [rq])) pouts
             end) phst.
Proof.
  intros.
  eapply atomic_hst_tinfo in H; eauto; subst.

  clear -H.
  induction phst; [constructor|].
  inv H; specialize (IHphst H3).
  constructor; auto.
  destruct a; auto.
  
  simpl in H2; clear -H2; destruct H2.
  split.

  - clear -H.
    induction mins; [constructor|].
    inv H; specialize (IHmins H3).
    constructor; auto.

    destruct a as [[msg oti] pred]; simpl in *.
    destruct oti; dest;
      unfold fromInternal, fromExternal in *; simpl in *; subst.
    + rewrite internal_not_external; auto.
    + unfold id; rewrite H0; auto.

  - clear -H0.
    induction mouts; [constructor|].
    inv H0; constructor; auto.
Qed.

Definition step_pred_t :=
  step_pred (stR:= PTStateR) step_t (@pToSystem TMsg) pToTLabel.

Theorem atomic_steps_pred_ok:
  forall sys ginv st1 thst st2 ts rqin mouts,
    InvStep sys step_t ginv ->
    steps step_t sys st1 thst st2 ->
    Atomic sys ts rqin thst mouts ->
    forall psys: PSystem TMsg,
      pToSystem psys = sys ->
      InvStep psys step_pred_t (LiftInv (@pstx_st _ _ PTStateR) ginv) /\
      exists pst1 phst pst2,
        pToTHistory phst = thst /\
        pstx_st pst1 = st1 /\
        pstx_st pst2 = st2 /\
        steps step_pred_t psys pst1 phst pst2.
Proof.
Admitted.

Lemma step_pred_rules_split:
  forall inds inits prules1 prules2 pst1 plbl pst2,
    step_pred_t {| psys_inds := inds;
                   psys_inits := inits;
                   psys_rules := prules1 ++ prules2 |} pst1 plbl pst2 ->
    step_pred_t {| psys_inds := inds;
                   psys_inits := inits;
                   psys_rules := prules1 |} pst1 plbl pst2 \/
    step_pred_t {| psys_inds := inds;
                   psys_inits := inits;
                   psys_rules := prules2 |} pst1 plbl pst2.
Proof.
Admitted.

Corollary step_pred_rules_split_addPRules_1:
  forall (psys: PSystem TMsg) prule prules pst1 plbl pst2,
    step_pred_t (addPRules (prule :: prules) (buildRawPSys _ psys)) pst1 plbl pst2 ->
    step_pred_t (addPRules [prule] (buildRawPSys _ psys)) pst1 plbl pst2 \/
    step_pred_t (addPRules prules (buildRawPSys _ psys)) pst1 plbl pst2.
Proof.
  intros.
  apply step_pred_rules_split; auto.
Qed.

Corollary step_pred_rules_split_addPRules_2:
  forall (psys: PSystem TMsg) prule1 prule2 prules pst1 plbl pst2,
    step_pred_t (addPRules (prule1 :: prule2 :: prules) (buildRawPSys _ psys)) pst1 plbl pst2 ->
    step_pred_t (addPRules [prule1] (buildRawPSys _ psys)) pst1 plbl pst2 \/
    step_pred_t (addPRules [prule2] (buildRawPSys _ psys)) pst1 plbl pst2 \/
    step_pred_t (addPRules prules (buildRawPSys _ psys)) pst1 plbl pst2.
Proof.
  intros.
  apply step_pred_rules_split_addPRules_1 in H; destruct H; auto.
  apply step_pred_rules_split_addPRules_1 in H; destruct H; auto.
Qed.

