Require Import Bool List String Peano_dec.
Require Import Common FMap ListSupport Syntax Semantics StepM StepT SemFacts.
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


(*! Some generic invariants for [MState] *)

Definition NoExtOutsMP {SysT} `{IsSystem SysT}
           (sys: SysT) (msgs: MessagePool Msg) :=
  ForallMP (fun midx tmsg => ~ In midx (merssOf sys)) msgs.

Definition NoExtOuts {SysT} `{IsSystem SysT}
           (sys: SysT) (st: MState) :=
  NoExtOutsMP sys (bst_msgs st).

Lemma step_m_no_rules_NoExtOuts:
  forall sys,
    sys_rules sys = nil ->
    forall st1,
      NoExtOuts sys st1 ->
      forall lbl st2,
        step_m sys st1 lbl st2 ->
        NoExtOuts sys st2.
Proof.
  unfold NoExtOuts, NoExtOutsMP; intros.
  inv H1; simpl in *; auto.
  - apply ForallMP_enqMsgs; auto.
    destruct H3.
    pose proof (merqsOf_merssOf_DisjList sys).
    eapply DisjList_SubList in H1; [|eassumption].

    clear -H1; induction eins; simpl; [constructor|].
    simpl in H1; apply DisjList_cons in H1; dest.
    constructor; auto.
  - apply ForallMP_deqMsgs; auto.
  - exfalso.
    rewrite H in H10; elim H10.
Qed.

Lemma steps_m_no_rules_NoExtOuts:
  forall sys,
    sys_rules sys = nil ->
    forall st1,
      NoExtOuts sys st1 ->
      forall ll st2,
        steps step_m sys st1 ll st2 ->
        NoExtOuts sys st2.
Proof.
  induction 3; simpl; intros; auto.
  eapply step_m_no_rules_NoExtOuts with (st1 := st2); eauto.
Qed.

Corollary behavior_no_rules_NoExtOuts:
  forall sys,
    sys_rules sys = nil ->
    forall ll st,
      steps step_m sys (initsOf sys) ll st ->
      NoExtOuts sys st.
Proof.
  intros.
  eapply steps_m_no_rules_NoExtOuts; eauto.
  apply ForallMP_emptyMP.
Qed.

(*! Some generic invariants for [TState] *)

Definition MsgsInInv (inv: TState -> Prop) :=
  forall oss orqs msgs trss trss' ts eins,
    inv {| tst_oss := oss; tst_orqs := orqs;
           tst_msgs := msgs; tst_trss := trss; tst_tid := ts |} ->
    inv {| tst_oss := oss; tst_orqs := orqs;
           tst_msgs := enqMsgs (imap toTMsgU eins) msgs;
           tst_trss := trss';
           tst_tid := ts |}.

Definition MsgsOutInv (inv: TState -> Prop) :=
  forall oss orqs msgs trss trss' ts eouts,
    inv {| tst_oss := oss; tst_orqs := orqs;
           tst_msgs := msgs; tst_trss := trss; tst_tid := ts |} ->
    inv {| tst_oss := oss; tst_orqs := orqs;
           tst_msgs := deqMsgs eouts msgs;
           tst_trss := trss';
           tst_tid := ts |}.

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
    inv H2; eauto.
    exfalso.
    rewrite H0 in H12.
    elim H12.
  Qed.
  
End Facts.

Definition WfDomOStates (dom: list IdxT) (oss: OStates) :=
  M.KeysEquiv oss dom.

Definition WfDomTState (dom: list IdxT) (tst: TState) :=
  WfDomOStates dom (tst_oss tst).

Definition TidLeMP (tmsgs: MessagePool TMsg) (tid: TrsId) :=
  ForallMP (fun _ tmsg =>
              match tmsg_info tmsg with
              | Some ti => tinfo_tid ti <= tid
              | None => True
              end) tmsgs.

Definition TidLtMP (tmsgs: MessagePool TMsg) (tid: TrsId) :=
  ForallMP (fun _ tmsg =>
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

Definition ValidTrss {SysT} `{IsSystem SysT}
           (sys: SysT) (tst: TState) :=
  extRssOf sys (tst_msgs tst) = extRssOf sys (tst_trss tst).

Lemma ValidTidState_MsgsInv:
  MsgsInv ValidTidState.
Proof.
  split; hnf; intros; hnf in *; cbn in *.
  - apply ForallMP_enqMsgs; auto.
    clear; induction eins; simpl; auto.
    constructor; auto.
    cbn; auto.
  - apply ForallMP_deqMsgs; auto.
Qed.

Lemma step_t_ValidTidState:
  forall st1,
    ValidTidState st1 ->
    forall sys lbl st2,
      step_t sys st1 lbl st2 ->
      ValidTidState st2.
Proof.
  unfold ValidTidState; intros.
  inv H0; auto.
  - hnf; hnf in H; simpl in *.
    apply ForallMP_enqMsgs; auto.
    clear; induction eins; [constructor|].
    constructor; simpl; auto.
  - hnf; hnf in H; simpl in *.
    apply ForallMP_deqMsgs; auto.
  - hnf; hnf in H; simpl in *.
    apply ForallMP_enqMsgs.
    + apply ForallMP_deqMsgs.
      eapply ForallMP_impl; eauto.
      clear -Hts; simpl; intros.
      destruct (tmsg_info m); auto.
      destruct (getTMsgsTInfo _); auto.
      omega.
    + apply Forall_impl with (Q:= fun idt => InMP (fst idt) (snd idt) msgs) in H5;
        [|intros; eapply FirstMP_InMP; eauto].
      eapply ForallMP_Forall_InMP in H5; eauto.

      clear -Hts H5.
      induction outs; [constructor|].
      constructor; auto.
      simpl; remember (getTMsgsTInfo (valsOf ins)) as ti; destruct ti; auto.
      apply eq_sym, getTMsgsTInfo_Some in Heqti.
      destruct Heqti as [tmsg [? ?]].
      unfold valsOf in H; apply in_map_iff in H.
      destruct H as [[midx mtmsg] [? ?]]; cbn in *; subst.
      eapply Forall_forall in H5; eauto.
      simpl in H5; rewrite H0 in H5; auto.
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
  eapply ForallMP_impl; eauto.
  simpl; intros.
  destruct (tmsg_info m); auto.
  omega.
Qed.

Lemma step_t_TidLt:
  forall st1 sys orule mins mouts st2,
    ValidTidState st1 ->
    mins <> nil ->
    step_t sys st1 (RlblInt orule mins mouts) st2 ->
    Forall (fun tmsg => tmsg_info tmsg = None) (valsOf mins) ->
    TidLt (tst_tid st2) st1.
Proof.
  intros; inv H1.
  simpl; rewrite getTMsgsTInfo_Forall_None by assumption.
  eapply TidLe_TidLt; eauto.
Qed.

Corollary step_t_tid_next_TidLt:
  forall sys st1 orule ins outs ts st2,
    ValidTidState st1 ->
    step_t sys st1 (RlblInt orule ins outs) st2 ->
    ins <> nil -> outs <> nil ->
    Forall (fun tmsg => tmsg_info tmsg = None) (valsOf ins) ->
    Forall (fun tmsg => match tmsg_info tmsg with
                        | Some ti => tinfo_tid ti = ts
                        | None => True
                        end) (valsOf outs) ->
    TidLt ts st1.
Proof.
  intros.
  replace ts with (tst_tid st2).
  - eauto using step_t_TidLt.
  - eauto using step_t_tid_next.
Qed.

Lemma step_t_rules_split:
  forall oinds minds merqs merss Hmvalid inits rules1 rules2 st1 lbl st2,
    step_t {| sys_oinds := oinds;
              sys_minds := minds;
              sys_merqs := merqs;
              sys_merss := merss;
              sys_msg_inds_valid := Hmvalid;
              sys_inits := inits;
              sys_rules := rules1 ++ rules2 |} st1 lbl st2 ->
    step_t {| sys_oinds := oinds;
              sys_minds := minds;
              sys_merqs := merqs;
              sys_merss := merss;
              sys_msg_inds_valid := Hmvalid;
              sys_inits := inits;
              sys_rules := rules1 |} st1 lbl st2 \/
    step_t {| sys_oinds := oinds;
              sys_minds := minds;
              sys_merqs := merqs;
              sys_merss := merss;
              sys_msg_inds_valid := Hmvalid;
              sys_inits := inits;
              sys_rules := rules2 |} st1 lbl st2.
Proof.
  intros.
  inv H.
  - left; constructor.
  - left; econstructor; eauto.
  - left; econstructor; eauto.
  - simpl in *.
    apply in_app_or in H8; destruct H8.
    + left; econstructor; eauto.
    + right; econstructor; eauto.
Qed.

