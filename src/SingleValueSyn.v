Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet SemFacts.
Require Import Simulation TrsSim Serial SerialFacts Predicate Synthesis SynthesisFacts.
Require Import Blocking.

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
      + Common.dest_in; cbn.
        * rewrite <-H; reflexivity.
        * rewrite <-H0; reflexivity.
        * rewrite <-H; reflexivity.
      + find_if_inside; auto.
        elim n; clear n.
        Common.dest_in.
        cbn in *.
        unfold svmIdxF in H.
        find_if_inside; auto.
    - find_if_inside.
      + Common.dest_in; cbn.
        * rewrite <-H; auto.
        * rewrite <-H0; auto.
        * rewrite <-H; auto.
      + find_if_inside; auto.
        elim n; clear n.
        Common.dest_in.
        cbn in *.
        unfold svmIdxF in H.
        find_if_inside; auto.
  Qed.

  Theorem impl0_ok: SynthOk spec SvmSim BlockedInv svmP impl0.
  Proof.
    split; [|split; [|split]].
    - eapply SvmSSS; econstructor.
    - vm_compute; intros; dest; exfalso; auto.
    - (* simulation & invariant *) admit.
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
        buildMsgId (mid_tid mid) (mid_from mid) (makeIdxExternal (mid_to mid)) (mid_chn mid).
      
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
        cbn in H; unfold makeIdxExternal in H.
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
      split; [|split; [|split]]; (* [SynthOk] consist of 5 conditions. *)
      try (rewrite addRulesSys_init; apply pimpl_ok; fail).

    Ltac trsSimulates_case_in msgF :=
      (** instantiation *)
      unfold TrsSimSepIn; intros; simpl;
      match goal with
      | [H: context[IlblIn ?min] |- context[step_det _ ?ist1 _ _] ] =>
        let ioss1 := fresh "ioss1" in
        let imsgs1 := fresh "imsgs1" in
        let its1 := fresh "its1" in
        destruct ist1 as [ioss1 imsgs1 its1];
        exists (toTMsgU (msgF (getMsg min)));
        exists {| tst_oss:= ioss1;
                  tst_msgs:= distributeMsg (toTMsgU (msgF (getMsg min))) imsgs1;
                  tst_tid:= its1;
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
      eapply trs_sim_in_atm_simulates;
      [trsSimulates_case_in msgF| | | | |].

    Ltac trsSimulates_atomic_trivial :=
      unfold TrsSimSepAtomic; intros;
      match goal with
      | [H: step_det _ _ _ _ |- _] => inv H
      end; [exfalso; eapply atomic_emptyILabel_not_in; eauto; simpl; tauto
           |exfalso; eapply atomic_iLblIn_not_in; eauto; simpl; tauto
           |].

    Definition svmTrsIdx0 := 0.
    Definition svmTargetOIdx0 := child1Idx.
    Definition svmTargetRuleIdx0 := 0.

    Definition svmRq0 (val: Value) :=
      {| msg_id := buildMsgId svmTrsIdx0 extIdx1 child1Idx rqChn;
         msg_value := val |}.

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
    Ltac svmR_child1_status_case_tac Hcase :=
      destruct Hcase as [iost1 [? [|[|]]]].

    (* Ltac build_rulesOf := *)
    (*   match goal with *)
    (*   | [H1: In ?obj (sys_objs _), H2: In _ (obj_rules ?obj) |- _] => *)
    (*     pose proof (rulesOf_in _ _ H1 _ H2) *)
    (*   end. *)

    Ltac simpl_addRulesSys :=
      repeat
        match goal with
        | [H: In _ (rulesOf (addRulesSys _ (buildRawSys _))) |- _] =>
          apply addRulesSys_buildRawSys_sublist in H
        | [H: context[isInternal (addRulesSys _ _)] |- _] =>
          rewrite addRulesSys_isInternal in H
        end.

    Ltac dest_ValidMsgId :=
      match goal with
      | [H: ValidMsgId _ _ _ (getMsg ?imsg) |- _] =>
        let imtid := fresh "imtid" in
        let imfrom := fresh "imfrom" in
        let imto := fresh "imto" in
        let imchn := fresh "imchn" in
        let imval := fresh "imval" in
        let itid := fresh "itid" in
        destruct imsg as [[[[imfrom imto imchn] imtid] imval] itid];
        let Hfrom := fresh "Hfrom" in
        let Hto := fresh "Hto" in
        let Hchn := fresh "Hchn" in
        destruct H as [Hfrom [Hto Hchn]];
        simpl in Hfrom, Hto, Hchn; subst
      end.

    Ltac synth_init_simpl :=
      (* build_rulesOf; *)
      simpl_addRulesSys;
      dest_ValidMsgId.

    Lemma addRulesO_makeRuleExternal:
      forall rs1 rs2 obj oidx eidx,
        oidx = obj_idx obj ->
        addRulesO (rs1 ++ map (makeRuleExternal oidx eidx) rs2) obj =
        addRulesO rs1 obj.
    Proof.
    Admitted.

    Lemma addRulesO_makePreCondDisj:
      forall rs1 rs2 obj rule (prec: PreCond) ost,
        rule_precond rule ost ->
        prec ost ->
        In rule (obj_rules (addRulesO (rs1 ++ map (makePreCondDisj prec) rs2) obj)) ->
        In rule (obj_rules (addRulesO rs1 obj)).
    Proof.
    Admitted.

    Ltac synth_sep_rules_obj tgt ext :=
      match goal with
      | [H: context[In ?rule (obj_rules (addRulesO ?rules _))] |- _] =>
        match type of rule with
        | Rule =>
          is_evar rules;
          instantiate (1:= _ ++ (map (makeRuleExternal tgt ext) _)) in H
        end
      end;
      rewrite addRulesO_makeRuleExternal in * by reflexivity.

    Ltac synth_sep_rules_prec prec :=
      match goal with
      | [H: context[In ?rule (obj_rules (addRulesO ?rules _))] |- _] =>
        match type of rule with
        | Rule =>
          is_evar rules;
          instantiate (1:= _ ++ (map (makePreCondDisj prec) _)) in H;
          eapply addRulesO_makePreCondDisj in H;
          [|eassumption|mv_rewriter; eassumption]
        end
      end.

    Ltac synth_obj_case_analysis sim rel caseF caseTac :=
      repeat
        match goal with
        | [H: sim _ ?sst1 |- _] =>
          let soss1 := fresh "soss1" in
          let smsgs1 := fresh "smsgs1" in
          let sts1 := fresh "sts1" in
          is_var sst1;
          destruct sst1 as [soss1 smsgs1 sts1];
          unfold sim in H; simpl in H
        | [H: rel _ _ |- _] =>
          let Hcase := fresh "Hcase" in
          pose proof H as Hcase;
          apply caseF in Hcase;
          caseTac Hcase
        end.

    Ltac synth_rq_rs_single trsIdx fromIdx curIdx toIdx rqPre rsPost rsOut :=
      match goal with
      | [H: context[In ?rule (obj_rules (addRulesO ?rules _))] |- _] =>
        match type of rule with
        | Rule =>
          is_evar rules;
          instantiate
            (1:= (synRq trsIdx curIdx alwaysLock fromIdx
                        (toIdx :: nil) rqPre)
                   :: (synRsSingle trsIdx curIdx toIdx rsPost rsOut)
                   :: nil) in H;
          Common.dest_in
        end
      end.

    Ltac synth_rq_correct sim_rq_tac :=
      (* To polish some hypotheses *)
      repeat
        match goal with
        | [H: rule_postcond (synRq _ _ _ _ _ _) _ _ _ |- _] =>
          simpl in H; unfold synRqPostcond in H; simpl in H; subst
        | [H: msg_id _ = rule_mid _ |- _] =>
          simpl in H; inv H
        end;
      (* Request-forwardings always correspond to silent steps in spec. *)
      simpl;
      (* To apply a custom Ltac to prove simulation *)
      sim_rq_tac.

    Ltac svmSim_rq_next :=
      hnf; simpl in *;
      eapply SvmR_EquivPreservingR; eauto;
      unfold StateEquivOS; intros;
      findeq.

    Ltac validOuts_tac :=
      simpl;
      repeat
        match goal with
        | [ |- context[?ov >>=[nil] _] ] => destruct ov; simpl
        | [ |- ValidOuts _ _ ] => split
        | [ |- Forall _ _] => constructor
        | [ |- NoDup _] => constructor
        | [ |- ~ In _ nil] => simpl; auto
        | [ |- _ /\ _] => split
        | [ |- _ = _] => reflexivity
        | [ |- _ <> _] => discriminate
        end.

    Ltac synth_spec_step p imsg specRule :=
      eapply SdInt;
      [auto (* [?nts > sts1] by setting a new timestamp
             * to [S sts1] *)
      |left; reflexivity (* [In ?obj spec]; [spec] usually
                          * has a single object *)
      |reflexivity
      |simpl; eassumption (* [spec] object should exist *)
      |instantiate (1:= {| tmsg_msg := p imsg |});
       reflexivity
      |repeat split (* [ValidMsgId] *)
      |
      |instantiate (1:= specRule); simpl; reflexivity
      |simpl; tauto (* [specRule] exists *)
      |auto (* [specRule] precondition is usually [True] *)
      |simpl; reflexivity (* [specRule] postcondition *)
      |reflexivity (* [specRule] outs *)
      |validOuts_tac (* [ValidOuts] *)
      |reflexivity (* about the [spec] timestamp *)
      ].

    Definition svmSynTrs0:
      { impl1: System & SynthOk spec SvmSim BlockedInv svmP impl1 }.
    Proof.
      syn_step_init impl0 impl0_ok.

      - (** simulation *)
        apply trsSimulates_trsInvHolds_rules_added;
          [apply impl0_ok|apply impl0_ok|repeat constructor| | | |].

        + (** [TrsSimulates] for newly added [Rule]s *)
          trsSimulates_trivial (svmMsgF extIdx1 extIdx2).

          * (** [TrsSimulates] for [Atomic] steps *)
            trsSimulates_atomic_trivial.

            (* 0) some initial simplification *)
            synth_init_simpl.

            (* 1) case analysis for each object; first for C1 *)
            destruct (obj_idx obj ==n child1Idx);
              [Common.dest_in; try discriminate|].
            { (* 1-1) separate rules; one for c1, another for the others *)
              synth_sep_rules_obj child1Idx child2Idx.

              (* 1-2) case analysis on c1 status *)
              synth_obj_case_analysis
                SvmSim SvmR SvmR_status_cases_1
                svmR_child1_status_case_tac.
              { (* 1-2-1) When C1.st = I *)
                synth_sep_rules_prec
                  (fun ost => (ost_st ost)@[statusIdx] = Some (VNat stI)).
                
                (* TODO: try to synthesize an immediate transaction;
                 * it should fail since it cannot have a mechanism to bring the 
                 * representative value from the other objects.
                 * When the trial fails, nothing is synthesized.
                 *)
                idtac.

                (* 1-2-2) Now try to synthesize "request-forwarding" and
                 * corresponding "responses-receiving" rules.
                 *)
                synth_rq_rs_single
                  svmTrsIdx0 extIdx1 child1Idx parentIdx
                  (fun ost => (ost_st ost)@[statusIdx] = Some (VNat stI))
                  (fun (pre: OState) v post =>
                     (ost_st post)@[statusIdx] = Some (VNat stS) /\
                     (ost_st post)@[valueIdx] = Some v)
                  (fun (st: StateT) (v: Value) => v).
                { (* 2-2-1: request-forwarding for C1 *)
                  synth_rq_correct svmSim_rq_next.
                }
                { (* 2-2-2: responses-back for C1 *)
                  simpl in *; inv H11.
                  unfold synRsOutsSingle.
                  remember ((ost_tst os)@[svmTrsIdx0]) as otrsh.
                  destruct otrsh;
                    [simpl|exfalso; admit (* need an invariant *)].
                  assert (tst_rqfrom t = extIdx1)
                    by admit. (* need an invariant *)
                  rewrite H6; simpl.

                  assert (exists sost,
                             soss1@[specIdx] = Some sost /\
                             (ost_st sost)@[valueIdx] = Some imval).
                  { admit. (* need an invariant *) }
                  destruct H9 as [sost [? ?]].

                  do 2 eexists; split.
                  { synth_spec_step
                      (svmMsgF extIdx1 extIdx2)
                      {| msg_id := buildMsgId svmTrsIdx0 extIdx1 child1Idx rsChn;
                         msg_value := imval |}
                      (specGetReq extIdx1 extIdx2 specChn1).

                    (* TODO:
                     * 1) Define simulation for [Messages] -- draining wrt. [tinfo_rqin].
                     * 2) Use the simulation and [BlockedInv] to prove this
                     *    ([firstM] to [firstM]).
                     *)
                    simpl.
                    admit.
                  }
                  { instantiate (1:= None); simpl.
                    rewrite H11; simpl.
                    split.
                    { unfold svmMsgF, getRespM, svmMsgIdF, buildMsgId; simpl.
                      admit. (* FIXME: specChn1 <> extIdx1 *)
                    }
                    { unfold SvmSim; simpl.
                      admit. (* need invariants *)
                    }
                  }
                }
              }
              { (* 1-2-2) When C1.st = S *) admit. }
              { (* 1-2-2) When C1.st = M *) admit. }
            }
            { (* For P and C2 *) admit. }

          * (** Global invariants hold for message-in steps. *)
            apply BlockedInv_in.

          * (** Global invariants hold for [Atomic] steps. *)
            admit.

          * (** Local invariant holds for the initial state. *)
            admit.

          * (** Local invariant holds for [Atomic] steps. *)
            admit.

        + (** Global invariants hold *)
          admit.
        + (** [trsPreservingSys]; to prove the synthesized rules are about a 
           *  single transaction.  *)
          admit.
        + (** [TrsDisj]; to prove the synthesized rules are disjoint with 
           *  previously synthesized rules. *)
          admit.

      - (** serializability *)
        admit.

    Admitted.
    
  End SynStep.

End Impl.

