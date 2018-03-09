Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet.
Require Import PredMsg StepPred.
Require Import Serial.

Lemma buildRawPSys_indicesOf:
  forall {SysT} `{IsSystem SysT OStates} (sys: SysT),
    indicesOf sys = indicesOf (buildRawPSys sys).
Proof.
  reflexivity.
Qed.

Corollary buildRawPSys_isExternal:
  forall {SysT} `{IsSystem SysT OStates} (sys: SysT),
    isExternal (buildRawPSys sys) = isExternal sys.
Proof.
  unfold isExternal; intros.
  rewrite <-buildRawPSys_indicesOf.
  reflexivity.
Qed.

Corollary buildRawPSys_isInternal:
  forall {SysT} `{IsSystem SysT OStates} (sys: SysT),
    isInternal (buildRawPSys sys) = isInternal sys.
Proof.
  unfold isInternal; intros.
  rewrite <-buildRawPSys_indicesOf.
  reflexivity.
Qed.

Lemma buildRawPSys_pToSystem_buildRawSys:
  forall {SysT} `{IsSystem SysT OStates} (sys: SysT),
    pToSystem (buildRawPSys sys) = buildRawSys sys.
Proof.
  reflexivity.
Qed.

Lemma addPRules_init:
  forall rules sys,
    initsOf (StateT:= OStates) (addPRules rules sys) =
    initsOf (StateT:= OStates) sys.
Proof.
  reflexivity.
Qed.

Lemma addPRules_indices:
  forall rules sys,
    indicesOf (addPRules rules sys) = indicesOf sys.
Proof.
  reflexivity.
Qed.

Corollary addPRules_isExternal:
  forall rules sys,
    isExternal (addPRules rules sys) =
    isExternal sys.
Proof.
  unfold isExternal; intros.
  rewrite addPRules_indices.
  reflexivity.
Qed.

Corollary addPRules_isInternal:
  forall rules sys,
    isInternal (addPRules rules sys) =
    isInternal sys.
Proof.
  unfold isInternal; intros.
  rewrite addPRules_indices.
  reflexivity.
Qed.

Corollary addPRules_behaviorOf:
  forall psys prules phst,
    behaviorOf (addPRules prules psys) phst = behaviorOf psys phst.
Proof.
  induction phst; [reflexivity|].
  simpl; rewrite IHphst; reflexivity.
Qed.

Lemma pToSystem_indices:
  forall psys, indicesOf psys = indicesOf (pToSystem psys).
Proof.
  reflexivity.
Qed.

Corollary pToSystem_isExternal:
  forall psys idx,
    isExternal psys idx = isExternal (pToSystem psys) idx.
Proof.
  unfold isExternal; intros.
  rewrite pToSystem_indices; reflexivity.
Qed.

Corollary pToSystem_isInternal:
  forall psys idx,
    isInternal psys idx = isInternal (pToSystem psys) idx.
Proof.
  unfold isInternal; intros.
  rewrite pToSystem_indices; reflexivity.
Qed.

Lemma pToTMsg_extOuts:
  forall psys ts rqin msgs,
    extOuts psys (map (fun pmsg => msgOfPMsg (projT2 pmsg)) msgs) =
    extOuts (pToSystem psys) (map tmsg_msg (map (pToTMsg ts rqin) msgs)).
Proof.
  induction msgs; simpl; intros; [reflexivity|].
  rewrite pToSystem_isExternal, IHmsgs.
  reflexivity.
Qed.

Lemma pToLabel_extLabel:
  forall psys ts rqin l,
    extLabel psys (pToLabel l) =
    extLabel (pToSystem psys) (iToLabel (pToTLabel ts rqin l)).
Proof.
  unfold extLabel; simpl; intros.
  destruct l; cbn.
  - reflexivity.
  - rewrite <-pToTMsg_extOuts; reflexivity.
Qed.

Lemma pToTHistory_behaviorOf:
  forall psys ts rqin phst,
    behaviorOf psys phst =
    behaviorOf (pToSystem psys) (pToTHistory ts rqin phst).
Proof.
  induction phst; simpl; intros; [reflexivity|].
  rewrite IHphst, <-pToLabel_extLabel; reflexivity.
Qed.

(** TODO: The current statement is wrong;
 * [psys] should have some more restrictions for the correctness of
 * _global_ preconditions wrt. the original system [sys].
 *)
Theorem steps_pred_ok:
  forall sys st1 thst st2 ts rqin mouts,
    steps_det sys st1 thst st2 ->
    Atomic sys ts rqin thst mouts ->
    forall psys,
      pToSystem psys = sys ->
      exists pst1 phst pst2,
        pToTState ts rqin pst1 = st1 /\
        pToTState ts rqin pst2 = st2 /\
        pToTHistory ts rqin phst = thst /\
        steps_pred psys pst1 phst pst2.
Proof.
Admitted.

Lemma step_pred_rules_split:
  forall inds inits prules1 prules2 pst1 plbl pst2,
    step_pred {| psys_inds := inds;
                 psys_inits := inits;
                 psys_rules := prules1 ++ prules2 |} pst1 plbl pst2 ->
    step_pred {| psys_inds := inds;
                 psys_inits := inits;
                 psys_rules := prules1 |} pst1 plbl pst2 \/
    step_pred {| psys_inds := inds;
                 psys_inits := inits;
                 psys_rules := prules2 |} pst1 plbl pst2.
Proof.
  intros.
  inv H.
  - left; constructor.
  - left; econstructor; auto.
  - simpl in *.
    apply in_app_or in H1; destruct H1.
    + left; econstructor; eauto.
    + right; econstructor; eauto.
  - simpl in *.
    apply in_app_or in H1; destruct H1.
    + left; econstructor; eauto.
    + right; econstructor; eauto.
  - simpl in *.
    apply in_app_or in H1; destruct H1.
    + left; econstructor; eauto.
    + right; econstructor; eauto.
Qed.

Corollary step_pred_rules_split_addPRules:
  forall psys prule prules pst1 plbl pst2,
    step_pred (addPRules (prule :: prules) (buildRawPSys psys)) pst1 plbl pst2 ->
    step_pred (addPRules [prule] (buildRawPSys psys)) pst1 plbl pst2 \/
    step_pred (addPRules prules (buildRawPSys psys)) pst1 plbl pst2.
Proof.
  intros.
  apply step_pred_rules_split; auto.
Qed.

