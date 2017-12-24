Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet SemFacts.
Require Import Simulation TrsSim Serial SerialFacts Predicate Synthesis SynthesisFacts.
Require Import AtomicSteps.

Require Import SingleValue SingleValueSim.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section Impl.
  Definition extIdx1 := 3.
  Definition extIdx2 := 4.
  (* Variables extIdx1 extIdx2: nat. *)

  Hypotheses (Hiext1: isExternal (impl0 extIdx1 extIdx2) extIdx1 = true)
             (Hiext2: isExternal (impl0 extIdx1 extIdx2) extIdx2 = true)
             (Hsext1: isExternal (spec extIdx1 extIdx2) extIdx1 = true)
             (Hsext2: isExternal (spec extIdx1 extIdx2) extIdx2 = true).

  Local Definition spec := spec extIdx1 extIdx2.
  Local Definition specObj := specObj extIdx1 extIdx2.
  Local Definition impl0 := impl0 extIdx1 extIdx2.
  Local Definition svmP := svmP extIdx1 extIdx2.

  Lemma svmMsgF_ValidMsgMap:
    ValidMsgMap (svmMsgF extIdx1 extIdx2) impl0 spec.
  Proof.
    unfold ValidMsgMap; intros.
    unfold svmMsgF; simpl.
    unfold svmIdxF, isInternal.
    unfold impl0.
    split.
    - find_if_inside.
      + reflexivity.
      + find_if_inside; auto.
        elim n; clear n.
        Common.dest_in.
        rewrite <-H.
        simpl; tauto.
    - find_if_inside.
      + reflexivity.
      + find_if_inside; auto.
        elim n; clear n.
        Common.dest_in.
        rewrite <-H.
        simpl; tauto.
  Qed.

  Theorem impl0_ok: SynthOk spec SvmSim svmP impl0.
  Proof.
    repeat split.
    - eapply SvmSSS; econstructor.
    - (* simulation *) admit.
    - (* serializability *) admit.
  Admitted.

  Section SynStep.

    Ltac get_target_trs impl oidx tidx pname :=
      let oobj := (eval cbn in (nth_error (sys_objs impl) oidx)) in
      match oobj with
      | Some ?obj =>
        let otrs := (eval cbn in (nth_error (obj_rules obj) tidx)) in
        match otrs with
        | Some ?trs => pose trs as pname
        end
      end.

    Ltac cbner t tn := let ct := (eval cbn in t) in pose ct as tn.
    Ltac hnfer t tn := let ht := (eval hnf in t) in pose ht as tn.

    Ltac get_rule_from trs pname :=
      cbner (mid_from (rule_mid trs)) pname.
    Ltac get_rule_precond trs pname :=
      cbner (rule_precond trs) pname.

    Ltac mv_rewriter :=
      repeat
        (match goal with
         | [H: Some _ = M.find _ _ |- _] => apply eq_sym in H
         | [H: None = M.find _ _ |- _] => apply eq_sym in H
         | [H1: M.find ?m ?k1 = Some _, H2: M.find ?m ?k2 = Some _ |- _] =>
           rewrite H1 in H2; inv H2
         | [H1: M.find ?m ?k1 = Some _, H2: M.find ?m ?k2 = None |- _] =>
           rewrite H1 in H2; discriminate
         end; simpl in *).

    (* If this Ltac succeeds, then provably [inv1] and [inv2] are 
     * not compatible for all state.
     * If it fails, then there's no information.
     *)
    Ltac inv_not_compatible inv1 inv2 :=
      let Hnc := fresh "Hnc" in
      assert (forall st, inv1 st -> inv2 st -> False)
        as Hnc by (cbn; intros; dest; intuition mv_rewriter);
      clear Hnc.

    Ltac find_new_prec cprec invs pname :=
      let hcprec := (eval hnf in cprec) in
      let hinvs := (eval hnf in invs) in
      match hinvs with
      | nil => fail
      | ?inv :: ?invs' =>
        tryif (inv_not_compatible hcprec inv)
        then (pose inv as pname)
        else find_new_prec hcprec invs'
      end.

    Section MakeExternal.
      Variables (targetIdx diffIdx: IdxT)
                (Hdiff: targetIdx <> diffIdx).
      
      Definition makeIdxExternal (idx: IdxT): IdxT :=
        if idx ==n targetIdx
        then diffIdx 
        else idx.
      
      Definition makeMsgIdExternal (mid: MsgId): MsgId :=
        {| mid_tid := mid_tid mid;
           mid_from := mid_from mid;
           mid_to := makeIdxExternal (mid_to mid);
           mid_chn := mid_chn mid
        |}.
      
      Definition makeRuleExternal (rule: Rule): Rule :=
        {| rule_mid := makeMsgIdExternal (rule_mid rule);
           rule_precond := rule_precond rule;
           rule_outs := rule_outs rule;
           rule_postcond := rule_postcond rule
        |}.

      Lemma makeRuleExternal_rule_in:
        forall rule rules1 rules2,
          mid_to (rule_mid rule) = targetIdx ->
          In rule (rules1 ++ map makeRuleExternal rules2) ->
          In rule rules1.
      Proof.
        intros.
        apply in_app_or in H0; destruct H0; auto.
        exfalso; clear -H H0 Hdiff.
        induction rules2; [auto|].
        destruct H0; auto.
        subst rule.
        simpl in H; unfold makeIdxExternal in H.
        find_if_inside; auto.
      Qed.

    End MakeExternal.

    Section MakePreCondDisj.
      Variable (prec: PreCond).

      Definition makePreCondDisj (rule: Rule): Rule :=
        {| rule_mid := rule_mid rule;
           rule_precond := fun ost => ~ (prec ost) /\ rule_precond rule ost;
           rule_outs := rule_outs rule;
           rule_postcond := rule_postcond rule
        |}.

      Lemma makePreCondDisj_rule_in:
        forall rule ost,
          rule_precond rule ost ->
          forall rules,
            In rule (map makePreCondDisj rules) ->
            ~ prec ost.
      Proof.
        induction rules; intros; [auto|].
        destruct H0; subst; auto.
        simpl in H; destruct H; auto.
      Qed.

    End MakePreCondDisj.

    Definition addPreCond (rule: Rule) (mid: MsgId) (prec: PreCond) :=
      {| rule_mid := mid;
         rule_precond := fun ost => rule_precond rule ost /\ prec ost;
         rule_outs := rule_outs rule;
         rule_postcond := rule_postcond rule |}.

    Ltac syn_step_init pimpl pimpl_ok :=
      econstructor;
      instantiate (1:= addRulesSys _ pimpl);
      split; [|split]; (* [SynthOk] consist of 3 conditions. *)
      [rewrite addRulesSys_init; apply pimpl_ok| |].

    Ltac trsSimulates_case_in msgF :=
      (** instantiation *)
      unfold TrsSimSteruleIn; intros; simpl;
      match goal with
      | [H: context[IlblIn ?min] |- context[step_det _ ?st1 _ _] ] =>
        let soss := fresh "soss" in
        let sims := fresh "sims" in
        let sts := fresh "sts" in
        destruct st1 as [soss sims sts];
        exists (toTMsgU (msgF (getMsg min)));
        exists {| tst_oss:= soss;
                  tst_msgs:= distributeMsg (toTMsgU (msgF (getMsg min))) sims;
                  tst_tid:= sts;
               |}
      end;
      (** some inversions *)
      repeat
        match goal with
        | [H: step_det _ _ (IlblIn _) _ |- _] => inv H
        end;
      (** construction *)
      repeat split;
      [|assumption (* simulation relation should be maintained *)];
      repeat econstructor;
      repeat
        match goal with
        | [H: isExternal _ (mid_from (msg_id _)) = true |-
           isExternal _ (mid_from (msg_id _)) = true] =>
          eapply validMsgMap_from_isExternal; [|eassumption]
        | [H: isInternal _ (mid_to (msg_id _)) = true |-
           isInternal _ (mid_to (msg_id _)) = true] =>
          eapply validMsgMap_to_isInternal; [|eassumption]
        | [ |- ValidMsgMap _ (addRulesSys _ (buildRawSys ?imp)) _ ] =>
          apply validMsgMap_same_indices with (impl1:= imp);
          [apply svmMsgF_ValidMsgMap
          |rewrite addRulesSys_indices, buildRawSys_indicesOf; reflexivity]
        end.

    (* This ltac handles trivial [Transactional] cases.
     * After then we only need to deal with [Atomic] histories.
     *)
    Ltac trsSimulates_trivial msgF :=
      apply trs_sim_in_atm_simulates;
      [unfold TrsSimSteruleIn; intros; trsSimulates_case_in msgF|].

    Ltac trsSimulates_atomic_trivial :=
      unfold TrsSimStepAtomic; intros;
      match goal with
      | [H: step_det _ _ _ _ |- _] => inv H
      end; [exfalso; eapply atomic_emptyILabel_not_in; eauto
           |exfalso; eapply atomic_iLblIn_not_in; eauto
           |].

    Definition svmTrsIdx0 := 0.
    Definition svmTargetOIdx0 := child1Idx.
    Definition svmTargetRuleIdx0 := 0.

    Definition svmRq0 (val: Value) :=
      {| msg_id := {| mid_tid := svmTrsIdx0;
                      mid_from := extIdx1;
                      mid_to := child1Idx;
                      mid_chn := rqChn |};
         msg_value := val |}.

    Record MsgInv :=
      { mi_from: IdxT;
        mi_to: IdxT;
        mi_chn: IdxT;
        mi_tid: IdxT;
        mi_inv: ObjectStates -> Prop
      }.

    Definition buildMsgInv from to chn tid inv :=
      {| mi_from:= from;
         mi_to:= to;
         mi_chn:= chn;
         mi_tid:= tid;
         mi_inv:= inv |}.

    Definition MsgInvs := list MsgInv.

    Definition MsgInvHolds (mi: MsgInv) (st: TState) :=
      forall q msg,
        findM (mi_from mi) (mi_to mi) (mi_chn mi) (tst_msgs st) = q ->
        In msg q ->
        tmsg_tid msg = Some (mi_tid mi) ->
        mi_inv mi (tst_oss st).

    Definition MsgInvsHold (mis: MsgInvs) (st: TState) :=
      Forall (fun mi => MsgInvHolds mi st) mis.

    Definition InvR0 (tid: IdxT): MsgInvs :=
      (buildMsgInv child1Idx parentIdx rsChn tid
                   (fun st =>
                      exists ost1,
                        st@[child1Idx] = Some ost1 /\
                        (ost_st ost1)@[statusIdx] = Some (VNat stI)))
        :: (buildMsgInv child2Idx parentIdx rsChn tid
                        (fun st =>
                           exists ost2,
                             st@[child2Idx] = Some ost2 /\
                             (ost_st ost2)@[statusIdx] = Some (VNat stI)))
        :: (buildMsgInv parentIdx child1Idx rsChn tid
                        (fun st =>
                           exists ost1 ost2,
                             st@[child1Idx] = Some ost1 /\
                             ((ost_st ost1)@[statusIdx] = Some (VNat stI) \/
                              (ost_st ost1)@[statusIdx] = Some (VNat stS)) /\
                             st@[child2Idx] = Some ost2 /\
                             ((ost_st ost2)@[statusIdx] = Some (VNat stI) \/
                              (ost_st ost2)@[statusIdx] = Some (VNat stS))))
        :: nil.

    Definition svmSynTrs0:
      { impl1: System & SynthOk spec SvmSim svmP impl1 }.
    Proof.
      syn_step_init impl0 impl0_ok.

      - (** simulation *)
        apply trsSimulates_rules_added.
        + apply impl0_ok.
        + repeat constructor.
        + (** simulation for newly added [Rule]s *)
          trsSimulates_trivial (svmMsgF extIdx1 extIdx2).
          trsSimulates_atomic_trivial.
          admit.
          
        + admit.
        + admit.

      - (** serializability *)
        admit.
        
    Admitted.
    
  End SynStep.

End Impl.

