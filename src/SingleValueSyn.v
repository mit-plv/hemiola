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
          prec ost ->
          forall rules1 rules2,
            In rule (rules1 ++ map makePreCondDisj rules2) ->
            In rule rules1.
      Proof.
        intros.
        apply in_app_or in H1; destruct H1; auto.
        exfalso; clear -H H0 H1.
        induction rules2; [auto|].
        destruct H1; auto.
        subst; cbn in H; destruct H; auto.
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

    Record RuleInv :=
      { ri_from: IdxT;
        ri_to: IdxT;
        ri_chn: IdxT;
        ri_inv: ObjectStates -> Prop
      }.

    Definition buildRuleInv from to chn inv :=
      {| ri_from:= from;
         ri_to:= to;
         ri_chn:= chn;
         ri_inv:= inv |}.

    Definition RuleInvs := list RuleInv.

    Fixpoint RuleExecuted (mfr mto mchn: IdxT) (hst: History) :=
      match hst with
      | nil => False
      | IlblOuts (Some hdl) _ :: hst' =>
        if mfr ==n mid_from (msg_id (tmsg_msg hdl))
        then if mto ==n mid_to (msg_id (tmsg_msg hdl))
             then if mchn ==n mid_chn (msg_id (tmsg_msg hdl))
                  then True
                  else RuleExecuted mfr mto mchn hst'
             else RuleExecuted mfr mto mchn hst'
        else RuleExecuted mfr mto mchn hst'
      | _ :: hst' => RuleExecuted mfr mto mchn hst'
      end.

    Definition RuleInvHolds (ri: RuleInv) (hst: History) (tst: TState) :=
      RuleExecuted (ri_from ri) (ri_to ri) (ri_chn ri) hst ->
      ri_inv ri (tst_oss tst).

    Definition RuleInvsHold (ris: RuleInvs) (hst: History) (tst: TState) :=
      Forall (fun ri => RuleInvHolds ri hst tst) ris.

    Lemma RuleInvsHold_nil:
      forall ris tst, RuleInvsHold ris nil tst.
    Proof.
      induction ris; intros; [constructor|].
      constructor; auto.
      - unfold RuleInvHolds; intros.
        exfalso; auto.
      - apply IHris.
    Qed.

    Ltac trsSimulates_case_in msgF :=
      (** instantiation *)
      unfold TrsSimStepMsgIn; intros; simpl;
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
    Ltac trsSimulates_trivial histInv msgF :=
      apply trs_sim_in_atm_simulates with (hinv:= histInv);
      [unfold TrsSimStepMsgIn; intros; trsSimulates_case_in msgF
      | |apply RuleInvsHold_nil].

    Ltac trsSimulates_atomic_trivial :=
      unfold TrsSimStepAtomic; intros;
      match goal with
      | [H: step_det _ _ _ _ |- _] => inv H
      end; [exfalso; eapply atomic_emptyILabel_not_in; eauto;
            eapply SubHistory_In; [firstorder|eauto]
           |exfalso; eapply atomic_iLblIn_not_in; eauto;
            eapply SubHistory_In; [firstorder|eauto]
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

    Definition trsInv0: RuleInvs :=
      (buildRuleInv child2Idx parentIdx rsChn
                    (fun st =>
                       exists ost2,
                         st@[child2Idx] = Some ost2 /\
                         (ost_st ost2)@[statusIdx] = Some (VNat stS) /\
                         (ost_st ost2)@[valueIdx] = Some VUnit))
        :: (buildRuleInv parentIdx child1Idx rsChn
                         (fun st =>
                            exists ostp ost2,
                              st@[parentIdx] = Some ostp /\
                              (ost_st ostp)@[statusIdx] = Some (VNat stS) /\
                              (ost_st ostp)@[valueIdx] = Some VUnit /\
                              st@[child2Idx] = Some ost2 /\
                              (ost_st ost2)@[statusIdx] = Some (VNat stS) /\
                              (ost_st ost2)@[valueIdx] = Some VUnit))
        :: nil.

    Lemma SvmR_status_cases_1:
      forall ioss soss,
        SvmR ioss soss ->
        exists iost1,
          ioss@[child1Idx] = Some iost1 /\
          ((ost_st iost1)@[statusIdx] = Some (VNat stI) \/
           (ost_st iost1)@[statusIdx] = Some (VNat stS) \/
           (ost_st iost1)@[statusIdx] = Some (VNat stM)).
    Proof.
      intros; inv H; eexists; eauto.
    Qed.

    Definition svmSynTrs0:
      { impl1: System & SynthOk spec SvmSim svmP impl1 }.
    Proof.
      syn_step_init impl0 impl0_ok.

      - (** simulation *)
        apply trsSimulates_rules_added.
        + apply impl0_ok.
        + repeat constructor.
        + (** simulation for newly added [Rule]s *)
          trsSimulates_trivial (RuleInvsHold trsInv0) (svmMsgF extIdx1 extIdx2).
          trsSimulates_atomic_trivial.

          (* +) some basic work *)
          pose proof (rulesOf_in _ _ H5 _ H12); clear H5 H12.
          apply addRulesSys_buildRawSys_sublist in H3.
          destruct fmsg as [[[mtid mfrom mto mchn] fval] ftid].
          destruct H9 as [? [? ?]]; simpl in *; subst.
          rewrite addRulesSys_isExternal in H8.
          
          (* 0) separate rules; one for c1, another for the others *)
          instantiate (1:= _ ++ (map (makeRuleExternal child1Idx child2Idx) _)).

          (* 1) case analysis on c1 status *)
          rename oss into ioss1.
          rename oims into imsgs1.
          rename ts into its1.
          destruct sst1 as [soss1 smsgs1 sts1].
          unfold SvmSim in H1; simpl in H1.
          pose proof (SvmR_status_cases_1 H1).
          destruct H5 as [iost1 [? ?]].
          destruct H6; [|destruct H6].

          * (* 2-1) When C1.st = I *)
            instantiate (2:= _ ++ (map (makePreCondDisj
                                          (fun ost => (ost_st ost)@[statusIdx] = Some (VNat stI)))
                                       _)).

            (* 2-2) Synthesize rules for C1, with [C1.st = I] as a precondition. *)
            destruct (obj_idx obj ==n child1Idx).
            { rewrite e in *.
              apply makeRuleExternal_rule_in in H3; [|discriminate|rewrite <-H11; reflexivity].
              eapply makePreCondDisj_rule_in in H3; [|eassumption|mv_rewriter; assumption].

              (* Try to synthesize an immediate transaction;
               * it fails since it cannot have a mechanism to bring the 
               * representative value from the other objects.
               * When the trial fails, nothing is synthesized.
               *)
              try
                (instantiate (3:= synImm svmTrsIdx0 child1Idx
                                         (fun ost => (ost_st ost)@[statusIdx] = Some (VNat stI))
                                         extIdx1 _ _ :: nil);
                 Common.dest_in;
                 fail).

              (* Now try to synthesize "request-forwarding" and corresponding
               * "responses-receiving" rules.
               *)
        
    Admitted.
    
  End SynStep.

End Impl.

