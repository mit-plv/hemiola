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

Definition MsgInInv (inv: TState -> Prop) :=
  forall oss orqs msgs ts emsg,
    inv {| tst_oss := oss; tst_orqs := orqs; tst_msgs := msgs; tst_tid := ts |} ->
    inv {| tst_oss := oss; tst_orqs := orqs;
           tst_msgs := enqMP (toTMsgU emsg) msgs; tst_tid := ts |}.

Section Facts.

  Lemma MsgInInv_invAnd:
    forall ginv1 ginv2,
      MsgInInv ginv1 ->
      MsgInInv ginv2 ->
      MsgInInv (ginv1 /\i ginv2).
  Proof.
    intros; hnf in *.
    intros; destruct H1.
    split; eauto.
  Qed.
    
  Lemma InvStep_no_rules:
    forall impl ginv,
      MsgInInv ginv ->
      sys_rules impl = nil ->
      InvStep impl step_t ginv.
  Proof.
    intros; hnf; intros.
    inv H2; auto.
    exfalso.
    rewrite H0 in H9.
    elim H9.
  Qed.
  
End Facts.

(*! Some general invariants *)

Definition WfDomOStates (dom: list IdxT) (oss: OStates) :=
  M.KeysEquiv oss dom.

Definition WfDomTState (dom: list IdxT) (tst: TState) :=
  WfDomOStates dom (tst_oss tst).

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

Lemma ValidTidState_MsgInInv:
  MsgInInv ValidTidState.
Proof.
  hnf; intros.
  hnf; hnf in H; intros.
  cbn in *.
  apply Forall_app; auto.
  repeat constructor.
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
    apply ForallMP_enqMP; auto.
    simpl; auto.
  - simpl; simpl in H.
    apply ForallMP_distributeMsgs.
    + apply ForallMP_removeMsgs.
      clear -H Hts.
      induction oims; simpl; [constructor|].
      inv H; constructor.
      * destruct (tmsg_info a); auto.
        destruct (getTMsgsTInfo msgs); omega.
      * apply IHoims; auto.
    + apply Forall_impl with (Q:= fun msg => InMP msg oims) in H4;
        [|intros; eapply FirstMP_InMP; eauto].
      apply ForallMP_InMP_SubList in H4.
      eapply ForallMP_SubList in H4; eauto.

      clear -Hts H4.
      apply Forall_filter.
      induction outs; [constructor|].
      constructor; auto.

      simpl; remember (getTMsgsTInfo msgs) as ti; destruct ti; auto.
      apply eq_sym, getTMsgsTInfo_Some in Heqti.
      destruct Heqti as [tmsg [? ?]].
      eapply ForallMP_forall in H4; eauto.
      rewrite H0 in H4; auto.
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
    step_t sys st1 (RlblOuts orule mins mouts) st2 ->
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
    step_t sys st1 (RlblOuts orule ins outs) st2 ->
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

Definition TInfoExists (sys: System) (tst: TState) :=
  ForallMP (fun tmsg =>
              if fromInternal sys tmsg
              then tmsg_info tmsg <> None
              else tmsg_info tmsg = None) (tst_msgs tst).

Lemma validMsgOuts_from_internal:
  forall {MsgT} `{HasMsg MsgT} sys idx,
    isInternal sys idx = true ->
    forall mouts: list MsgT,
      ValidMsgOuts idx mouts ->
      ForallMP (fun msg => fromInternal sys msg = true) mouts.
Proof.
  induction mouts; simpl; intros; [constructor|].
  destruct H1; inv H1; inv H2; inv H5; dest.
  constructor.
  - simpl in H0; unfold id in H0.
    unfold fromInternal; simpl; rewrite H0; reflexivity.
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
    apply ForallMP_enqMP; auto.
    unfold fromInternal; simpl.
    rewrite external_not_internal by assumption; reflexivity.
  - simpl; simpl in H.
    apply ForallMP_distributeMsgs.
    + apply ForallMP_removeMsgs; auto.
    + pose proof (idx_in_sys_internal _ _ H1).
      eapply validMsgOuts_from_internal in H10; eauto.
      clear -H10; simpl in H10.
      induction outs; [constructor|].
      inv H10.
      simpl; unfold toInternal; simpl.
      destruct (isInternal sys (mid_to (msg_id a))); auto.
      constructor; cbn.
      * unfold fromInternal in *; cbn in *.
        unfold id in H1; rewrite H1; discriminate.
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
  - simpl in *.
    apply in_app_or in H6; destruct H6.
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

