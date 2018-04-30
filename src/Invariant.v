Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepT SemFacts.
Require Import Serial.

Require Import Omega.

Set Implicit Arguments.

Section Invariant.
  Variables (SysI StateI LabelI: Type).
  Context `{IsSystem SysI} `{HasInit SysI StateI} `{HasLabel LabelI}.

  Variable (impl: SysI).

  Variables (stepI: Step SysI StateI LabelI)
            (ginv: StateI -> Prop).

  Definition Invariant := StateI -> Prop.

  Definition InvInit := ginv (initsOf impl).

  Definition InvStep :=
    forall ist1,
      ginv ist1 ->
      forall lbl ist2,
        stepI impl ist1 lbl ist2 ->
        ginv ist2.

  Definition InvSteps :=
    forall ist1,
      ginv ist1 ->
      forall lbl ist2,
        steps stepI impl ist1 lbl ist2 ->
        ginv ist2.

  Hypotheses (Hinvi: InvInit)
             (Hinvs: InvStep).

  Lemma inv_steps':
    forall ist1,
      ginv ist1 ->
      forall ihst ist2,
        steps stepI impl ist1 ihst ist2 ->
        ginv ist2.
  Proof.
    induction 2; simpl; intros; eauto.
  Qed.

  Lemma inv_steps: InvSteps.
  Proof.
    unfold InvSteps; intros.
    eapply inv_steps'; eauto.
  Qed.
  
End Invariant.

Section Operations.
  Context {StateT: Type}.

  Definition invAnd (inv1 inv2: Invariant StateT) :=
    fun tst => inv1 tst /\ inv2 tst.

  Definition invImp (inv1 inv2: Invariant StateT) :=
    forall tst, inv1 tst -> inv2 tst.

  Lemma tinv_proj1: forall inv1 inv2, invImp (invAnd inv1 inv2) inv1.
  Proof. firstorder. Qed.
  Lemma tinv_proj2: forall inv1 inv2, invImp (invAnd inv1 inv2) inv2.
  Proof. firstorder. Qed.

  Lemma inv_split:
    forall (inv1 inv2: Invariant StateT) st,
      inv1 st ->
      inv2 st ->
      (invAnd inv1 inv2) st.
  Proof.
    unfold invAnd; intros; dest; split; eauto.
  Qed.

End Operations.

Ltac split_inv := apply inv_split.

Infix "/\i" := invAnd (at level 80).
Infix "->i" := invImp (at level 99).

(*! Some generic invariants *)

Definition MsgsInInv (inv: TState -> Prop) :=
  forall oss orqs msgs ts eins,
    inv {| tst_oss := oss; tst_orqs := orqs; tst_msgs := msgs; tst_tid := ts |} ->
    inv {| tst_oss := oss; tst_orqs := orqs;
           tst_msgs := distributeMsgs (toTMsgsU eins) msgs; tst_tid := ts |}.

Definition MsgsOutInv (inv: TState -> Prop) :=
  forall oss orqs msgs ts eouts,
    inv {| tst_oss := oss; tst_orqs := orqs; tst_msgs := msgs; tst_tid := ts |} ->
    inv {| tst_oss := oss; tst_orqs := orqs;
           tst_msgs := removeMsgs eouts msgs; tst_tid := ts |}.

Definition MsgsInv := MsgsInInv /\i MsgsOutInv.

Section Facts.

  Lemma MsgsInInv_invAnd:
    forall ginv1 ginv2,
      MsgsInInv ginv1 ->
      MsgsInInv ginv2 ->
      MsgsInInv (ginv1 /\i ginv2).
  Proof.
    intros; hnf in *.
    intros; destruct H1.
    split; eauto.
  Qed.

  Lemma MsgsOutInv_invAnd:
    forall ginv1 ginv2,
      MsgsOutInv ginv1 ->
      MsgsOutInv ginv2 ->
      MsgsOutInv (ginv1 /\i ginv2).
  Proof.
    intros; hnf in *.
    intros; destruct H1.
    split; eauto.
  Qed.

  Lemma MsgsInv_invAnd:
    forall ginv1 ginv2,
      MsgsInv ginv1 ->
      MsgsInv ginv2 ->
      MsgsInv (ginv1 /\i ginv2).
  Proof.
    intros; simpl.
    destruct H, H0.
    split.
    - apply MsgsInInv_invAnd; auto.
    - apply MsgsOutInv_invAnd; auto.
  Qed.

  Lemma InvStep_no_rules:
    forall impl ginv,
      MsgsInv ginv ->
      sys_rules impl = nil ->
      InvStep impl step_t ginv.
  Proof.
    intros; hnf; intros.
    destruct H.
    inv H2; auto.
    exfalso.
    rewrite H0 in H11.
    elim H11.
  Qed.
  
End Facts.

Definition WfDomOStates (dom: list IdxT) (oss: OStates) :=
  M.KeysEquiv oss dom.

Definition WfDomTState (dom: list IdxT) (tst: TState) :=
  WfDomOStates dom (tst_oss tst).

Definition TInfoExists (sys: System) (tst: TState) :=
  ForallMP (fun tmsg =>
              if fromInternal sys tmsg
              then tmsg_info tmsg <> None
              else tmsg_info tmsg = None) (tst_msgs tst).

Definition TidLeMP (tmsgs: MessagePool TMsg) (tid: TrsId) :=
  ForallMP (fun tmsg =>
              match tmsg_info tmsg with
              | Some ti => tinfo_tid ti <= tid
              | None => True
              end) tmsgs.

Definition TidLtMP (tmsgs: MessagePool TMsg) (tid: TrsId) :=
  ForallMP (fun tmsg =>
              match tmsg_info tmsg with
              | Some ti => tinfo_tid ti < tid
              | None => True
              end) tmsgs.

Definition TidLe (tid: TrsId) (tst: TState) :=
  TidLeMP (tst_msgs tst) tid.

Definition TidLt (tid: TrsId) (tst: TState) :=
  TidLtMP (tst_msgs tst) tid.

Definition ValidTidState (tst: TState) :=
  TidLe (tst_tid tst) tst.

Definition NoExtOutsMP (sys: System) (tmsgs: MessagePool TMsg) :=
  Forall (fun tmsg => toExternal sys tmsg = false) tmsgs.

Definition NoExtOuts (sys: System) (tst: TState) :=
  NoExtOutsMP sys (tst_msgs tst).

Lemma ValidTidState_MsgsInv:
  MsgsInv ValidTidState.
Proof.
  hnf; intros.
  split.
  - hnf; intros; hnf in H; intros.
    cbn in *.
    apply Forall_app; auto.
    clear; induction eins; [constructor|].
    simpl; constructor; simpl; auto.
  - hnf; intros; hnf in H; intros.
    cbn in *.
    hnf; cbn.
    apply ForallMP_removeMsgs; auto.
Qed.

Lemma step_t_ValidTidState:
  forall st1,
    ValidTidState st1 ->
    forall sys lbl st2,
      step_t sys st1 lbl st2 ->
      ValidTidState st2.
Proof.
  unfold ValidTidState; intros; inv H0; auto.
  - simpl; simpl in H.
    apply ForallMP_distributeMsgs; auto.
    clear; induction eins; [constructor|].
    constructor; simpl; auto.
  - simpl; simpl in H.
    apply ForallMP_removeMsgs; auto.
  - simpl; simpl in H.
    apply ForallMP_distributeMsgs.
    + apply ForallMP_removeMsgs.
      clear -H Hts.
      induction msgs; simpl; [constructor|].
      inv H; constructor.
      * destruct (tmsg_info a); auto.
        destruct (getTMsgsTInfo ins); omega.
      * apply IHmsgs; auto.
    + apply Forall_impl with (Q:= fun msg => InMP msg msgs) in H5;
        [|intros; eapply FirstMP_InMP; eauto].
      apply ForallMP_InMP_SubList in H5.
      eapply ForallMP_SubList in H5; eauto.

      clear -Hts H5.
      induction outs; [constructor|].
      constructor; auto.

      simpl; remember (getTMsgsTInfo ins) as ti; destruct ti; auto.
      apply eq_sym, getTMsgsTInfo_Some in Heqti.
      destruct Heqti as [tmsg [? ?]].
      eapply ForallMP_forall in H5; eauto.
      rewrite H0 in H5; auto.
Qed.

Lemma steps_t_ValidTidState:
  forall st1,
    ValidTidState st1 ->
    forall sys hst st2,
      steps step_t sys st1 hst st2 ->
      ValidTidState st2.
Proof.
  induction 2; simpl; intros; auto.
  apply step_t_ValidTidState in H1; auto.
Qed.

Lemma TidLe_TidLt:
  forall ts nts tst,
    TidLe ts tst ->
    nts > ts ->
    TidLt nts tst.
Proof.
  unfold TidLe, TidLt, TidLeMP, TidLtMP; intros.
  eapply Forall_impl; eauto.
  simpl; intros.
  destruct (tmsg_info a); auto.
  omega.
Qed.

Lemma step_t_TidLt:
  forall st1 sys orule mins mouts st2,
    ValidTidState st1 ->
    mins <> nil ->
    step_t sys st1 (RlblInt orule mins mouts) st2 ->
    Forall (fun tmsg => tmsg_info tmsg = None) mins ->
    TidLt (tst_tid st2) st1.
Proof.
  intros; inv H1; [elim H0; reflexivity|].
  simpl; rewrite getTMsgsTInfo_Forall_None by assumption.
  eapply TidLe_TidLt; eauto.
Qed.

Corollary step_t_tid_next_TidLt:
  forall sys st1 orule ins outs ts st2,
    ValidTidState st1 ->
    step_t sys st1 (RlblInt orule ins outs) st2 ->
    ins <> nil -> outs <> nil ->
    Forall (fun tmsg => tmsg_info tmsg = None) ins ->
    Forall (fun tmsg => match tmsg_info tmsg with
                        | Some ti => tinfo_tid ti = ts
                        | None => True
                        end) outs ->
    TidLt ts st1.
Proof.
  intros.
  replace ts with (tst_tid st2).
  - eauto using step_t_TidLt.
  - eauto using step_t_tid_next.
Qed.

Lemma validMsgOuts_from_internal:
  forall {MsgT} `{HasMsg MsgT} sys idx,
    isInternal sys idx = true ->
    forall mouts: list MsgT,
      ValidMsgsOut idx mouts ->
      ForallMP (fun msg => fromInternal sys msg = true) mouts.
Proof.
  induction mouts; simpl; intros; [constructor|].
  destruct H1; inv H1; inv H2; inv H5; dest.
  constructor.
  - simpl in H0; unfold_idx.
    rewrite H0; reflexivity.
  - apply IHmouts; split; auto.
Qed.

Lemma step_t_tinfo:
  forall sys st1,
    TInfoExists sys st1 ->
    forall lbl st2,
      step_t sys st1 lbl st2 ->
      TInfoExists sys st2.
Proof.
  unfold TInfoExists; intros; inv H0; auto.
  - simpl; simpl in H.
    apply ForallMP_distributeMsgs; auto.
    destruct H2.
    clear -H0; induction eins; [constructor|].
    inv H0; dest.
    specialize (IHeins H3).
    simpl; constructor; auto.
    unfold_idx; simpl.
    destruct (ma_from _ ?<n _); congruence.
  - simpl; simpl in H.
    apply ForallMP_removeMsgs; auto.
  - simpl; simpl in H.
    apply ForallMP_distributeMsgs.
    + apply ForallMP_removeMsgs; auto.
    + pose proof (idx_in_sys_internal _ _ H2).
      eapply validMsgOuts_from_internal in H11; eauto.
      clear -H11; simpl in H11.
      induction outs; [constructor|].
      inv H11.
      simpl; constructor; cbn.
      * unfold fromInternal in *; simpl in *.
        unfold id in H1; rewrite H1.
        discriminate.
      * apply IHouts; auto.
Qed.

Lemma step_t_rules_split:
  forall inds inits rules1 rules2 st1 lbl st2,
    step_t {| sys_inds := inds;
                sys_inits := inits;
                sys_rules := rules1 ++ rules2 |} st1 lbl st2 ->
    step_t {| sys_inds := inds;
                sys_inits := inits;
                sys_rules := rules1 |} st1 lbl st2 \/
    step_t {| sys_inds := inds;
                sys_inits := inits;
                sys_rules := rules2 |} st1 lbl st2.
Proof.
  intros.
  inv H.
  - left; constructor.
  - left; econstructor; eauto.
  - left; econstructor; eauto.
  - simpl in *.
    apply in_app_or in H7; destruct H7.
    + left; econstructor; eauto.
    + right; econstructor; eauto.
Qed.

Lemma steps_t_tinfo:
  forall sys st1,
    TInfoExists sys st1 ->
    forall hst st2,
      steps step_t sys st1 hst st2 ->
      TInfoExists sys st2.
Proof.
  induction 2; simpl; intros; auto.
  apply step_t_tinfo in H1; auto.
Qed.

Lemma step_t_no_rules_NoExtOuts:
  forall sys,
    sys_rules sys = nil ->
    forall st1,
      NoExtOuts sys st1 ->
      forall lbl st2,
        step_t sys st1 lbl st2 ->
        NoExtOuts sys st2.
Proof.
  unfold NoExtOuts, NoExtOutsMP; intros.
  inv H1; simpl in *; auto.
  - apply ForallMP_distributeMsgs; auto.
    destruct H3.
    clear -H1; induction eins; simpl; [constructor|].
    inv H1; dest.
    constructor.
    + unfold toInternal, toExternal in *; simpl in *.
      unfold id in H0.
      apply internal_not_external; auto.
    + apply IHeins; auto.
  - apply ForallMP_removeMsgs; auto.
  - exfalso.
    rewrite H in H9; elim H9.
Qed.

Lemma steps_t_no_rules_NoExtOuts:
  forall sys,
    sys_rules sys = nil ->
    forall st1,
      NoExtOuts sys st1 ->
      forall ll st2,
        steps step_t sys st1 ll st2 ->
        NoExtOuts sys st2.
Proof.
  induction 3; simpl; intros; auto.
  eapply step_t_no_rules_NoExtOuts with (st1 := st2); eauto.
Qed.

Corollary behavior_no_rules_NoExtOuts:
  forall sys,
    sys_rules sys = nil ->
    forall ll st,
      steps step_t sys (initsOf sys) ll st ->
      NoExtOuts sys st.
Proof.
  intros.
  eapply steps_t_no_rules_NoExtOuts; eauto.
  constructor.
Qed.
  
