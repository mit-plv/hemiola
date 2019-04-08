Require Import Bool List String Peano_dec.
Require Import Common FMap HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsTopo RqRsMsgPred RqRsCorrect.

Require Import Msi MsiSv SpecSv MsiSvTopo.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Section Inv.

  Definition ImplOStateI (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] = msiI.

  Definition ImplOStateS (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] = msiI \/
    (ost#[implStatusIdx] = msiS /\ ost#[implValueIdx] = cv).

  Definition ImplOStateM (cv: nat) (ost: OState ImplOStateIfc): Prop :=
    ost#[implStatusIdx] = msiM /\ ost#[implValueIdx] = cv.

  Definition ImplStateI (oss: OStates ImplOStateIfc): Prop.
  Proof.
    refine ((oss@[parentIdx]) >>=[False] (fun post => _)).
    refine ((oss@[child1Idx]) >>=[False] (fun cost1 => _)).
    refine ((oss@[child2Idx]) >>=[False] (fun cost2 => _)).
    exact (ImplOStateI post /\ (* Directory status is I as well. *)
           ImplOStateI cost1 /\ ImplOStateI cost2).
  Defined.

  Definition ImplStateS (cv: nat) (oss: OStates ImplOStateIfc): Prop.
  Proof.
    refine ((oss@[parentIdx]) >>=[False] (fun post => _)).
    refine ((oss@[child1Idx]) >>=[False] (fun cost1 => _)).
    refine ((oss@[child2Idx]) >>=[False] (fun cost2 => _)).
    refine (post#[implStatusIdx] = msiS /\ _). (* Directory status is S. *)
    exact (ImplOStateS cv cost1 /\ ImplOStateS cv cost2).
  Defined.

  Definition ImplStateM (cv: nat) (oss: OStates ImplOStateIfc): Prop.
  Proof.
    refine ((oss@[parentIdx]) >>=[False] (fun post => _)).
    refine ((oss@[child1Idx]) >>=[False] (fun cost1 => _)).
    refine ((oss@[child2Idx]) >>=[False] (fun cost2 => _)).
    refine (post#[implStatusIdx] = msiM /\ _). (* Directory status is M. *)
    exact ((ImplOStateM cv cost1 /\ ImplOStateI cost2) \/
           (ImplOStateI cost1 /\ ImplOStateM cv cost2)).
  Defined.

  Definition ImplMsg (cv: nat) (msg: Msg) :=
    In (msg_id msg) [msiRsS; msiRsM; msiDownRsS; msiDownRsM] ->
    msg_value msg = VNat cv.

  Definition ImplQ (cv: nat) (midx: IdxT) (q: Queue Msg) :=
    In midx impl.(sys_minds) ->
    Forall (ImplMsg cv) q.

  Definition ImplMsgs (cv: nat) (msgs: MessagePool Msg) :=
    ForallQ (fun midx q => ImplQ cv midx q) msgs.

  Definition ImplStateCoherent
             (cv: nat) (st: MState ImplOStateIfc): Prop :=
    (ImplStateI st.(bst_oss) \/
     ImplStateS cv st.(bst_oss) \/
     ImplStateM cv st.(bst_oss)) /\
    ImplMsgs cv st.(bst_msgs).
  
  Definition ImplStateMSI (st: MState ImplOStateIfc): Prop :=
    exists cv, (* The coherent value always exists. *)
      ImplStateCoherent cv st.

  Section Facts.

    Lemma msiSv_impl_InvTrs_ext_in:
      forall st1 eins st2,
        ImplStateMSI st1 ->
        step_m impl st1 (RlblIns eins) st2 ->
        ImplStateMSI st2.
    Proof.
      intros; inv_step.
      destruct H as [cv ?]; exists cv.
      destruct H; simpl in *.
      split; simpl; auto.
      clear H.

      do 3 (red in H0; red).
      intros; specialize (H0 _ H).
      rewrite findQ_not_In_enqMsgs; [assumption|].
      eapply DisjList_In_1; [|eassumption].
      eapply DisjList_SubList; [apply H3|].
      apply DisjList_comm, sys_minds_sys_merqs_DisjList.
    Qed.

    Lemma msiSv_impl_InvTrs_ext_out:
      forall st1 eouts st2,
        ImplStateMSI st1 ->
        step_m impl st1 (RlblOuts eouts) st2 ->
        ImplStateMSI st2.
    Proof.
      intros; inv_step.
      destruct H as [cv ?]; exists cv.
      destruct H; simpl in *.
      split; simpl; auto.
      clear H.

      do 3 (red in H0; red).
      intros; specialize (H0 _ H).
      rewrite findQ_not_In_deqMsgs; [assumption|].
      eapply DisjList_In_1; [|eassumption].
      eapply DisjList_SubList; [apply H4|].
      apply DisjList_comm, sys_minds_sys_merss_DisjList.
    Qed.

    (** TODO: define it. *)
    Definition MsiSvMsgOutPred: MsgOutPred ImplOStateIfc :=
      fun eout oss =>
        True.

    Lemma msiSvMsgOutPred_good:
      GoodMsgOutPred topo MsiSvMsgOutPred.
    Proof.
    Admitted.

    (** TODO: define it. *)
    Definition msiSvMsgOutBoundF (inits: list (Id Msg)): list (Id Msg) :=
      nil.
    
    Lemma msiSv_impl_InvTrs: InvTrs impl ImplStateMSI.
    Proof.
      eapply inv_atomic_InvTrs;
        [red; intros; eapply msiSv_impl_InvTrs_ext_in; eauto
        |red; intros; eapply msiSv_impl_InvTrs_ext_out; eauto
        |].
      instantiate (1:= AtomicMsgOutsInv MsiSvMsgOutPred msiSvMsgOutBoundF).

      red; intros.
      destruct H1.

      generalize dependent ist2.
      induction H3; simpl; intros; subst.
        
    Admitted.

    Lemma ImplStateMSI_init:
      ImplStateMSI (initsOf impl).
    Proof.
      repeat red.
      exists 0; split.
      - right; left.
        repeat split; right; split; reflexivity.
      - constructor.
    Qed.

    Lemma ImplStateMSI_invStep:
      InvStep impl step_m ImplStateMSI.
    Proof.
      apply invSeq_serializable_invStep.
      - apply ImplStateMSI_init.
      - apply inv_trs_seqSteps.
        apply msiSv_impl_InvTrs.
      - eapply rqrs_Serializable.
        apply msiSv_impl_RqRsSys.
    Qed.

  End Facts.
  
End Inv.

Section Sim.

  Local Definition spec := SpecSv.spec 1.
  Local Definition impl := MsiSv.impl.

  (** Simulation between states *)

  Definition SpecState (v: nat) (oss: OStates SpecOStateIfc): Prop.
  Proof.
    refine ((oss@[specIdx]) >>=[False] (fun sost => _)).
    exact (sost#[specValueIdx] = v).
  Defined.

  Definition SimMSI: MState ImplOStateIfc -> MState SpecOStateIfc -> Prop :=
    fun ist sst =>
      exists cv,
        ImplStateCoherent cv ist /\
        SpecState cv sst.(bst_oss).

  Section Facts.

    Lemma SimMsiSv_init:
      SimMSI (initsOf impl) (initsOf spec).
    Proof.
      repeat red.
      exists 0; split.
      - split.
        + right; left.
          repeat split; right; split; reflexivity.
        + constructor.
      - reflexivity.
    Qed.

    Lemma SimMsiSv_sim:
      InvSim step_m step_m ImplStateMSI SimMSI impl spec.
    Proof.
      red; intros.

      (** TODO: simulation proof should be very easy when equipped with 
       *        sufficient invariants, by iterating all possible state 
       *        transitions by rules.
       *        Automate this process.
       *)
      inv H2.
    Admitted.
    
    Theorem MsiSv_ok:
      (steps step_m) # (steps step_m) |-- impl ⊑ spec.
    Proof.
      apply invSim_implies_refinement
        with (ginv:= ImplStateMSI)
             (sim:= SimMSI).
      - apply SimMsiSv_sim.
      - apply ImplStateMSI_invStep.
      - apply SimMsiSv_init.
      - apply ImplStateMSI_init.
    Qed.

  End Facts.
  
End Sim.

