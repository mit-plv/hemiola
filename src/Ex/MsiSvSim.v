Require Import Bool List String Peano_dec.
Require Import Common FMap HVector Syntax Topology Semantics SemFacts StepM.
Require Import Invariant TrsInv Simulation Serial SerialFacts.
Require Import RqRsTopo RqRsFacts RqRsMsgPred RqRsCorrect RqRsLang.

Require Import Msi MsiSv SpecSv MsiSvTopo.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Definition Mii := (IdxT * IdxT)%type.

Definition mii_dec: forall mii1 mii2: Mii, {mii1 = mii2} + {mii1 <> mii2}.
Proof.
  decide equality.
  - apply eq_nat_dec.
  - apply eq_nat_dec.
Defined.

Definition miis_dec := list_eq_dec mii_dec.

Definition miiOf (idm: Id Msg): Mii := (idOf idm, msg_id (valOf idm)).
Definition miisOf (msgs: list (Id Msg)): list Mii :=
  map miiOf msgs.

Definition AtomicMsgOutsInv {oifc} (mp: MsgOutPred oifc)
           (abf: list Mii -> list Mii):
  list (Id Msg) -> list (Id Msg) -> MState oifc -> MState oifc -> Prop :=
  fun inits eouts pst nst =>
    SubList (miisOf eouts) (abf (miisOf inits)) /\
    Forall (fun eout => mp eout nst.(bst_oss)) eouts.

Ltac disc_AtomicMsgOutsInv :=
  match goal with
  | [H: AtomicMsgOutsInv _ _ _ _ _ _ |- _] => destruct H
  end.

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

    Notation "A <-- OA ; CONT" :=
      (OA >>=[False] (fun A => CONT)) (at level 15, right associativity).

    Fixpoint caseDec {A B} (dec: forall a1 a2: A, {a1 = a2} + {a1 <> a2})
             (a: A) (def: B) (cs: list (A * B)) :=
      match cs with
      | nil => def
      | (ca, cp) :: cs' =>
        if dec a ca then cp else caseDec dec a def cs'
      end.

    Notation "x : t" := (x, t) (at level 90, only parsing): cases_scope.
    Notation "| xt1 | xt2 | .. | xtn" :=
      (cons xt1 (cons xt2 .. (cons xtn nil) ..)) (at level 95, only parsing): cases_scope.
    Delimit Scope cases_scope with cases.
    Notation "'match' 'case' X 'on' DEC 'default' DEF 'with' CS 'end'" :=
      (caseDec DEC X DEF CS%cases) (only parsing).

    Definition MsiSvMsgOutPred: MsgOutPred ImplOStateIfc :=
      fun eout oss =>
        post <-- oss@[parentIdx];
          cost1 <-- oss@[child1Idx];
          cost2 <-- oss@[child2Idx];
          match case (miiOf eout)
                     on mii_dec
                     default True
          with
          | (pc1, msiRsS): 
              post#[implStatusIdx] = msiS /\ cost2#[implStatusIdx] = msiS
          | (pc2, msiRsS):
              post#[implStatusIdx] = msiS /\ cost1#[implStatusIdx] = msiS
          | (pc1, msiRsM): 
              post#[implStatusIdx] = msiM /\ cost2#[implStatusIdx] = msiI
          | (pc2, msiRsM):
              post#[implStatusIdx] = msiM /\ cost1#[implStatusIdx] = msiI
          | (c1pRs, msiDownRsS): cost1#[implStatusIdx] = msiS
          | (c2pRs, msiDownRsS): cost2#[implStatusIdx] = msiS
          | (c1pRs, msiDownRsM): cost1#[implStatusIdx] = msiI
          | (c2pRs, msiDownRsM): cost2#[implStatusIdx] = msiI
          end.

    Lemma msiSvMsgOutPred_good:
      GoodMsgOutPred topo MsiSvMsgOutPred.
    Proof.
    Admitted.

    Definition msiSvAtomicBoundF (inits: list Mii): list Mii :=
      match case inits on miis_dec default nil with
      | [(ec1, Spec.getRq)]:
          [(ce1, Spec.getRs); (c1pRq, msiRqS); (pc1, msiRsS);
             (pc2, msiDownRqS); (c2pRs, msiDownRsS)]
      | [(ec1, Spec.setRq)]:
          [(ce1, Spec.setRs); (c1pRq, msiRqM); (pc1, msiRsM);
             (pc2, msiDownRqM); (c2pRs, msiDownRsM)]
      | [(ec1, Spec.evictRq)]:
          [(ce1, Spec.evictRs); (c1pRq, msiRqI); (pc1, msiRsI)]
      | [(ec2, Spec.getRq)]:
          [(ce2, Spec.getRs); (c2pRq, msiRqS); (pc2, msiRsS);
             (pc1, msiDownRqS); (c1pRs, msiDownRsS)]
      | [(ec2, Spec.setRq)]:
          [(ce2, Spec.setRs); (c2pRq, msiRqM); (pc2, msiRsM);
             (pc1, msiDownRqM); (c1pRs, msiDownRsM)]
      | [(ec2, Spec.evictRq)]:
          [(ce2, Spec.evictRs); (c2pRq, msiRqI); (pc2, msiRsI)]
      end.

    Ltac disc_rule_custom ::=
      try disc_AtomicMsgOutsInv.

    Ltac atomic_non_init_bound_exfalso_step :=
      match goal with
      | [H1: SubList [_] ?eouts, H2: SubList (miisOf ?eouts) _ |- _] =>
        let Hs := fresh "H" in
        pose proof (SubList_trans (SubList_map miiOf H1) H2) as Hs;
        clear -Hs; apply SubList_singleton_In in Hs; cbn in Hs
      | [H: context[miis_dec ?miis1 ?miis2] |- _] =>
        destruct (miis_dec miis1 miis2) in H;
        try (dest_in; discriminate)
      end.

    Ltac atomic_non_init_bound_exfalso :=
      exfalso;
      disc_rule_conds; solve_rule_conds_const;
      repeat atomic_non_init_bound_exfalso_step.
    
    Lemma msiSv_impl_InvTrs: InvTrs impl ImplStateMSI.
    Proof.
      eapply inv_atomic_InvTrs;
        [red; intros; eapply msiSv_impl_InvTrs_ext_in; eauto
        |red; intros; eapply msiSv_impl_InvTrs_ext_out; eauto
        |].
      instantiate (1:= AtomicMsgOutsInv MsiSvMsgOutPred msiSvAtomicBoundF).

      red; intros.
      destruct H1.

      generalize dependent ist2.
      induction H3; simpl; intros; subst.
      - admit.

      - inv_steps.
        specialize (IHAtomic H1 _ H9); dest.
        (** For each rule, *)
        inv_step; dest_in.

        + atomic_non_init_bound_exfalso.
        + atomic_non_init_bound_exfalso.
        + 
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

