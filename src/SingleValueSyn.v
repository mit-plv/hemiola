Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet SemFacts.
Require Import Simulation Serial SerialFacts Invariant TrsSim.
Require Import PredMsg StepPred PredMsgFacts.
Require Import Synthesis SynthesisFacts Blocking.

Require Import SingleValue SingleValueSim.

Require Import Omega.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section Impl.
  Definition extIdx1 := 3.
  Definition extIdx2 := 4.
  (* Variables extIdx1 extIdx2: nat. *)

  Hypotheses (Hiext1: isExternal impl0 extIdx1 = true)
             (Hiext2: isExternal impl0 extIdx2 = true)
             (Hsext1: isExternal (spec extIdx1 extIdx2) extIdx1 = true)
             (Hsext2: isExternal (spec extIdx1 extIdx2) extIdx2 = true).

  Local Definition spec := spec extIdx1 extIdx2.
  Local Definition svmMsgIdF := svmMsgIdF extIdx1.
  Local Definition svmMsgF := svmMsgF extIdx1.
  Local Definition svmP := svmP extIdx1.
  Local Definition SvmSim := SvmSim extIdx1.

  Lemma svmMsgF_ValidMsgMap:
    ValidMsgMap svmMsgF impl0 spec.
  Proof.
    unfold ValidMsgMap; intros.
    unfold svmMsgF; simpl.
    unfold svmIdxF, fromInternal, toInternal, isInternal.
    unfold impl0.
    split.
    - find_if_inside.
      + Common.dest_in; cbn in *.
        * unfold id in H; rewrite <-H; reflexivity.
        * unfold id in H0; rewrite <-H0; reflexivity.
        * unfold id in H; rewrite <-H; reflexivity.
      + find_if_inside; auto.
        elim n; clear n.
        Common.dest_in.
        cbn in *.
        unfold svmIdxF in H.
        find_if_inside; auto.
    - find_if_inside.
      + Common.dest_in; cbn in *.
        * unfold id in H; rewrite <-H; auto.
        * unfold id in H0; rewrite <-H0; auto.
        * unfold id in H; rewrite <-H; auto.
      + find_if_inside; auto.
        elim n; clear n.
        Common.dest_in.
        cbn in *.
        unfold svmIdxF in H.
        find_if_inside; auto.
  Qed.

  Definition SvmInvs := SvmInv /\i BlockedInv.

  Ltac red_SvmInvs :=
    repeat 
      match goal with
      | [H: SvmInvs _ |- _] => inv H
      end.

  Ltac red_SvmSim :=
    repeat
      match goal with
      | [H: SvmSim _ _ |- _] => destruct H
      | [H: SvmR _ _ |- _] =>
        let cv := fresh "cv" in
        destruct H as [cv [? ?]]
      | [H: SpecState _ _ |- _] =>
        let sost := fresh "sost" in
        destruct H as [sost [? ?]]
      | [H1: ImplStateMSI ?ioss ?v1, H2: ImplStateMSI ?ioss ?v2 |- _] =>
        assert (v1 = v2) by eauto using impl_state_MSI_value_eq; subst v1
      end.

  Ltac red_svm := red_SvmInvs; red_SvmSim.

  Theorem impl0_ok: SynthOk spec SvmSim SvmInvs svmP impl0.
  Proof.
    split; [|split; [|split]].
    - (* simulation for the initial states *) admit.
    - (* invariant holds for the initial states *) admit.
    - (* simulation & invariant *) admit.
    - (* serializability *) admit.
  Admitted.

  Section SynStep.

    Ltac syn_step_init pimpl pimpl_ok :=
      econstructor;
      instantiate (1:= addRules _ pimpl);
      split; [|split; [|split]]; (* [SynthOk] consist of 4 conditions. *)
      [apply pimpl_ok|apply pimpl_ok| |].

    Ltac trs_sim_init pimpl_ok :=
      apply trsSimulates_trsInvHolds_rules_added; intros;
      [apply pimpl_ok|apply pimpl_ok|repeat constructor| | | |].

    Ltac trs_simulates_case_slt :=
      unfold TrsSimSilent; intros;
      (** inversions *)
      match goal with
      | [H: step_det _ _ emptyRLabel _ |- _] => inv H
      end;
      (** constructions *)
      eexists; split; [econstructor|assumption].

    Ltac trs_simulates_case_in msgF sim :=
      (** instantiation *)
      unfold TrsSimIn; intros; simpl;
      match goal with
      | [H: context[RlblIn ?min] |- context[step_det _ ?ist1 _ _] ] =>
        let ioss1 := fresh "ioss1" in
        let imsgs1 := fresh "imsgs1" in
        let its1 := fresh "its1" in
        destruct ist1 as [ioss1 imsgs1 its1];
        exists (toTMsgU (msgF (getMsg min)));
        exists {| tst_oss:= ioss1;
                  tst_msgs:= enqMP (toTMsgU (msgF (getMsg min))) imsgs1;
                  tst_tid:= its1;
               |}
      end;
      (** inversions *)
      repeat
        match goal with
        | [H: step_det _ _ (RlblIn _) _ |- _] => inv H
        | [H: sim _ _ |- _] => inv H
        end;
      (** constructions *)
      repeat split;
      [|assumption (* simulation relation should be maintained *)
       |simpl; apply SimMP_ext_msg_in; auto];
      repeat econstructor;
      unfold fromExternal, toInternal in *;
      repeat
        match goal with
        | [H: isExternal _ (mid_from (msg_id _)) = true |-
           isExternal _ (mid_from (msg_id _)) = true] =>
          eapply validMsgMap_from_isExternal; [|eassumption]
        | [H: isInternal _ (mid_to (msg_id _)) = true |-
           isInternal _ (mid_to (msg_id _)) = true] =>
          eapply validMsgMap_to_isInternal; [|eassumption]
        | [ |- ValidMsgMap _ (addRules _ (buildRawSys ?imp)) _ ] =>
          apply validMsgMap_same_indices with (impl1:= imp);
          [apply svmMsgF_ValidMsgMap
          |rewrite addRules_indices, <-buildRawSys_indicesOf; reflexivity]
        end.
    
    (* This ltac handles trivial [Transactional] cases.
     * After then we only need to deal with [Atomic] histories.
     *)
    Ltac trs_simulates_trivial msgF sim :=
      eapply trs_sim_in_atm_simulates;
      [trs_simulates_case_slt
      |trs_simulates_case_in msgF sim
      |].

    Ltac clear_atomic_hyps :=
      repeat
        match goal with
        | [H: Atomic _ _ _ _ ?mouts |- _] => clear H; clear mouts
        | [H: InvStep _ step_det _ |- _] => clear H
        end.

    Ltac reduce_invstep_pred :=
      repeat
        match goal with
        | [H: InvStep _ (step_pred (StateT:= TState)) _ /\ _ |- _] => destruct H
        | [H: exists (_: PTState) (_: PHistory TMsg) (_: PTState), _ |- _] =>
          let pst1 := fresh "pst1" in
          let phst := fresh "phst" in
          let pst2 := fresh "pst2" in
          destruct H as [pst1 [phst [pst2 ?]]]; dest; subst
        | [H: forall _, _ = _ -> _ |- _] => specialize (H _ eq_refl)
        end.
    
    Ltac trs_simulates_atomic_to_steps_pred :=
      unfold TrsSimAtomic; intros;
      match goal with
      | [H1: Atomic _ _ _ ?hst _, H2: steps step_det _ _ ?hst _ |- _] =>
        pose proof (atomic_history_pred_start H1 H2)
      end;
      match goal with
      | [H: steps step_det (addRules _ (buildRawSys ?implTopo)) _ _ _ |- _] =>
        eapply steps_pred_ok with (psys:= addPRules _ (buildRawPSys _ implTopo)) in H;
        eauto; [clear_atomic_hyps; reduce_invstep_pred|]
      end.

    Ltac inv_lift inv :=
      match goal with
      | [H: inv (?f ?ist) |- _] =>
        change (inv (f ist)) with (LiftInv f inv ist) in H
      end.

    Ltac sim_liftL sim :=
      match goal with
      | [H: sim (?f ?ist) ?sst |- _] =>
        change (sim (f ist) sst) with (LiftSimL f sim ist sst) in H
      end.

    Ltac reduce_addPRules :=
      repeat
        match goal with
        | [ |- context[indicesOf (addPRules _ _)] ] =>
          rewrite addPRules_indices
        | [ |- context[isExternal (addPRules _ _)] ] =>
          rewrite addPRules_isExternal
        | [ |- context[isInternal (addPRules _ _)] ] =>
          rewrite addPRules_isInternal
        | [ |- context[behaviorOf (addPRules _ _)] ] =>
          rewrite addPRules_behaviorOf
        | [H: context[indicesOf (addPRules _ _)] |- _] =>
          rewrite addPRules_indices in H
        | [H: context[isExternal (addPRules _ _)] |- _] =>
          rewrite addPRules_isExternal in H
        | [H: context[isInternal (addPRules _ _)] |- _] =>
          rewrite addPRules_isInternal in H
        | [H: context[behaviorOf (addPRules _ _)] |- _] =>
          rewrite addPRules_behaviorOf in H
        end.

    Ltac reduce_addRules :=
      repeat
        match goal with
        | [ |- context[indicesOf (addRules _ _)] ] =>
          rewrite addRules_indices
        | [ |- context[isExternal (addRules _ _)] ] =>
          rewrite addRules_isExternal
        | [ |- context[isInternal (addRules _ _)] ] =>
          rewrite addRules_isInternal
        | [ |- context[behaviorOf (addRules _ _)] ] =>
          rewrite addRules_behaviorOf
        | [H: context[indicesOf (addRules _ _)] |- _] =>
          rewrite addRules_indices in H
        | [H: context[isExternal (addRules _ _)] |- _] =>
          rewrite addRules_isExternal in H
        | [H: context[isInternal (addRules _ _)] |- _] =>
          rewrite addRules_isInternal in H
        | [H: context[behaviorOf (addRules _ _)] |- _] =>
          rewrite addRules_behaviorOf in H
        end.

    Ltac reduce_sim_steps_to_step_proof :=
      repeat
        (match goal with
         | [H: exists _ _, _ |- exists _ _, _] =>
           let sst2 := fresh "sst2" in
           let shst := fresh "shst" in
           destruct H as [sst2 [shst ?]]; dest;
           exists sst2, shst
         | [ |- _ /\ _] => split; eauto
         | [H: map _ (behaviorOf (buildRawPSys _ ?implTopo) _) = ?lhs |-
            map _ (behaviorOf (buildRawSys ?implTopo) _) = ?lhs] =>
           erewrite <-buildRawPSys_pToSystem_buildRawSys, <-pToTHistory_behaviorOf;
           eassumption
         end; reduce_addPRules; reduce_addRules).

    Ltac reduce_sim_steps_to_step_clear tinv tsim :=
      repeat
        match goal with
        | [H: steps _ _ _ _ _ |- _] => clear H
        | [H: Forall _ ?hst |- _] =>
          (* This might be too strong; would there be a better match? *)
          clear H; try clear hst
        | [H: tinv _ |- _] => clear H
        | [H: tsim _ _ |- _] => clear H
        end.

    Ltac reduce_sim_steps_to_step tinv tsim :=
      match goal with
      | [H: steps ?stI _ _ _ _ |- context[steps ?stS _ _ _ _] ] =>
        eapply inv_simulation_steps
          with (stepS:= stS) (ginv:= tinv) (sim:= tsim) in H; eauto;
        [reduce_sim_steps_to_step_proof|reduce_sim_steps_to_step_clear tinv tsim]
      end.

    Ltac inv_sim_init stepI :=
      unfold InvSim; intros;
      repeat
        match goal with
        | [H: stepI _ _ ?ilbl _ |- _] =>
          is_var ilbl;
          let orule := fresh "orule" in
          let mins := fresh "mins" in
          let mouts := fresh "mouts" in
          destruct ilbl as [|orule mins mouts];
          (* Each label from an [Atomic] history cannot be a [LblIn] case. *)
          [intuition idtac|]
        end.

    Ltac sim_pred_silent :=
      repeat
        match goal with
        | [H: step_pred _ _ (PlblOuts ?orule _ _) _ |- _] =>
          is_var orule;
          let rule := fresh "rule" in destruct orule as [rule|]
        | [H: step_pred _ _ (PlblOuts None _ _) _ |- _] =>
          inv H; simpl; auto
        end.

    Record PStackElt :=
      { pste_rr: RqRs;
        pste_pmid: PMsgId;
        pste_prec: PRPrecond }.

    Ltac pstack_empty :=
      set (nil (A:= PStackElt)) as stack.

    Ltac pstack_enq tid rr from to chn prec pred :=
      match goal with
      | [st: list PStackElt |- _] =>
        let stack := fresh "stack" in
        set ({| pste_rr := rr;
                pste_pmid :=
                  {| pmid_mid :=
                       {| mid_addr :=
                            {| ma_from := from;
                               ma_to := to;
                               ma_chn := chn |};
                          mid_tid := tid |};
                     pmid_pred := pred
                  |};
                pste_prec := prec |} :: st) as stack; subst st
      end.

    Ltac pstack_first :=
      match goal with
      | [st:= ?hd :: _ : list PStackElt |- _] =>
        constr:(hd)
      end.

    Ltac pstack_deq :=
      match goal with
      | [st:= _ :: ?tl : list PStackElt |- _] =>
        let stack := fresh "stack" in
        set tl as stack; subst st
      end.

    Ltac pstack_clear :=
      match goal with
      | [st: list PStackElt |- _] => clear st
      end.

    Definition buildPRuleImmFromPStack (pste: PStackElt) (dchn: IdxT) :=
      PRuleImm TMsg (pste_pmid pste)
               (dualOfP (pste_pmid pste) dchn)
               (pste_prec pste).

    Ltac synth_prule :=
      match goal with
      | [H: step_pred (addPRules ?rules _) _ _ _ |- _] =>
        is_evar rules; instantiate (1:= _ :: _);
        apply step_pred_rules_split_addPRules in H;
        destruct H
      end.

    Ltac pstack_deq_instantiate_imm_prule :=
      match goal with
      | [H: step_pred (addPRules [?rule] _) _ _ _ |- _] =>
        is_evar rule;
        let pfst := pstack_first in
        instantiate (1:= buildPRuleImmFromPStack pfst rsChn) in H;
        pstack_clear
      end.

    Ltac step_pred_invert_imm :=
      repeat
        match goal with
        | [H: step_pred _ _ (PlblOuts (Some _) _ _) _ |- _] => inv H
        | [H: In _ (psys_rules _) |- _] => inv H; try discriminate
        | [H: In _ nil |- _] => inv H
        | [H: ?rule = _ |- _] =>
          match type of rule with
          | PRule _ => inv H
          end
        end.

    Ltac step_pred_invert_dest_pmsg :=
      repeat
        match goal with
        | [H: DualPMsg ?rq ?rs |- _] =>
          is_var rq; is_var rs;
          let rqfrom := fresh "rqfrom" in
          let rqto := fresh "rqto" in
          let rqchn := fresh "rqchn" in
          let rqtid := fresh "rqtid" in
          let rqpred := fresh "rqpred" in
          let rqval := fresh "rqval" in
          let rsfrom := fresh "rsfrom" in
          let rsto := fresh "rsto" in
          let rschn := fresh "rschn" in
          let rstid := fresh "rstid" in
          let rspred := fresh "rspred" in
          let rsval := fresh "rsval" in
          destruct rq as [[[[[rqfrom rqto rqchn] rqtid] rqval] rqinfo] rqpred];
          destruct rs as [[[[[rsfrom rsto rschn] rstid] rsval] rsinfo] rspred];
          cbn in *
        | [H: DualPMsg {| pmsg_omsg := _; pmsg_pred := _ |}
                       {| pmsg_omsg := _; pmsg_pred := _ |} |- _] => inv H
        | [H: DualMid {| mid_addr := _; mid_tid := _ |}
                      {| mid_addr := _; mid_tid := _ |} |- _] => inv H
        | [H: dualOf _ _ = _ |- _] => inv H
        | [H: {| pmid_mid := _; pmid_pred := _ |} = _ |- _] => inv H
        | [H: _ = {| pmid_mid := _; pmid_pred := _ |} |- _] => inv H
        | [H: {| mid_addr := _; mid_tid := _ |} = _ |- _] => inv H
        | [H: _ = {| mid_addr := _; mid_tid := _ |} |- _] => inv H
        end.

    Ltac red_forall :=
      repeat
        match goal with
        | [H: Forall _ nil |- _] => inv H
        | [H: Forall _ (_ :: nil) |- _] => inv H
        end.

    Ltac red_ValidMsgsIn :=
      repeat
        match goal with
        | [H: ValidMsgsIn _ _ |- _] => inv H
        end.

    Ltac clear_useless :=
      repeat
        match goal with
        | [H: ?t = ?t |- _ ] => clear H
        end.

    Ltac red_LiftInv :=
      repeat 
        match goal with
        | [H: LiftInv _ _ _ |- _] => hnf in H
        end.

    Ltac red_LiftSimL :=
      repeat
        match goal with
        | [H: LiftSimL _ _ _ _ |- _] => hnf in H
        end.

    Ltac red_pred :=
      repeat
        match goal with
        | [H: ?pred _ _ _ _ |- _] =>
          match type of pred with
          | Pred => hnf in H
          end
        end.

    Ltac step_pred_invert_red red_custom :=
      repeat (step_pred_invert_dest_pmsg;
              red_forall;
              red_ValidMsgsIn;
              red_LiftInv;
              red_LiftSimL;
              red_pred;
              clear_useless;
              red_custom;
              dest; cbn in *; subst).

    Ltac sim_spec_constr_init ruleS :=
      repeat
        match goal with
        | [ |- context[step_det _ ?sst _ _] ] =>
          is_var sst;
          let soss := fresh "soss" in
          let smsgs := fresh "smsgs" in
          let stid := fresh "stid" in
          destruct sst as [soss smsgs stid]
        | [ |- exists (sst: TState), _] => eexists
        | [ |- exists (slbl: TLabel), _] =>
          eexists (RlblOuts (Some ruleS) (toTMsgU _ :: nil) _)
        end.

    Ltac sim_spec_constr_split :=
      repeat
        match goal with
        | [ |- _ /\ _] => split
        end.

    Ltac sim_spec_constr_step :=
      repeat
        (try match goal with
             | [ |- step_det _ _ _ _] => econstructor
             | [ |- _ > _] => auto
             | [ |- In _ _] => simpl; tauto
             | [ |- ~ In _ nil] =>
               let Hx := fresh "Hx" in
               intro Hx; elim Hx
             | [ |- Forall _ (_ :: _)] => constructor
             | [ |- Forall _ nil] => constructor
             | [ |- FirstMP _ _] =>
               eapply blocked_SimMP_FirstMP; eauto;
               [apply pmsg_omsg_FirstMP; eassumption|reflexivity]
             | [ |- ValidMsgsIn _ _] => repeat constructor
             | [ |- ValidMsgOuts _ _] => repeat constructor
             | [ |- rule_postcond _ _ _ _ _] => repeat constructor
             end;
         try reflexivity;
         try discriminate;
         try eassumption;
         mred_find).

    Ltac sim_spec_constr_extLabel_eq :=
      match goal with
      | [ |- _ = Some (LblOuts ?outs) ] =>
        instantiate (1:= toTMsgs _ outs)
      end;
      reflexivity.

    Ltac sim_spec_constr srule :=
      sim_spec_constr_init srule;
      sim_spec_constr_split;
      (* Prove the external label equality first, *)
      [|sim_spec_constr_extLabel_eq|];
      (* and then the actual step relation. *)
      [sim_spec_constr_step|].
    
    Definition svmTrsIdx0: TrsId := SvmGetE.

    Definition svmSynTrs0:
      { impl1: System & SynthOk spec SvmSim SvmInvs svmP impl1 }.
    Proof.
      syn_step_init impl0 impl0_ok.

      - (** Simulation and preservation of global invariants. *)
        trs_sim_init impl0_ok.

        + (** [TrsSimulates] for newly added [Rule]s *)
          trs_simulates_trivial svmMsgF SvmSim.

          (** [TrsSimAtomic]: [TrsSimulates] for [Atomic] steps. *)
          (* Now convert the target [Atomic] [steps_det] into [steps_pred].
           * We will have two subgoals, one for synthesizing predicate rules
           * and the other for synthesizing actual executable rules, using
           * already-synthesized predicate rules.
           *)
          trs_simulates_atomic_to_steps_pred.

          * (** Synthesis of [PRules]. *)

            (* Reduce steps-to-steps to a step-to-step proof. *)
            inv_lift SvmInvs.
            sim_liftL SvmSim.
            reduce_sim_steps_to_step
              (LiftInv pToTState SvmInvs)
              (LiftSimL pToTState SvmSim).

            (** Prove [InvSim], a (step-)simulation from [step_pred] to [step_det]: *)
            inv_sim_init (step_pred (StateT:= TState)).

            (* Prove simulation for silent steps, which is trivial. *)
            sim_pred_silent.

            (* Prove simulation for internal steps, 
             * and synthesize predicate rules simultaneously.
             *)

            (* A job stack will be used to track 
             * which rules should be synthesized now. *)
            pstack_empty.

            (* Add initial requests. *)
            pstack_enq svmTrsIdx0 Rq extIdx1 child1Idx rqChn ImplOStatusI getPred.
            pstack_enq svmTrsIdx0 Rq extIdx1 child1Idx rqChn ImplOStatusS getPred.
            pstack_enq svmTrsIdx0 Rq extIdx1 child1Idx rqChn ImplOStatusM getPred.

            (* Dequeue the first element of [list PStackElt] and
             * try to synthesize an immediate [PRule].
             *)
            synth_prule; [|pstack_deq].
            { (** Try to synthesize an immediate [PRule]. *)
              (* TODO: need an Ltac checker to check this immediate rule can 
               * handle the current request or not.
               *)
              pstack_deq_instantiate_imm_prule.

              (** Inversion of a step by impl. *)

              (* Since the target rule is immediate, inversion of a step should
               * generate only one subgoal.
               *)
              step_pred_invert_imm.

              (* After inverting a step, lots of reductions are required 
               * to prove the simulation. 
               *)
              step_pred_invert_red red_svm.

              (** Construction of a step by spec *)
              sim_spec_constr (specGetReq extIdx1 extIdx1).

              cbn; split; cbn.
              { exists rsval; split.
                { rewrite <-H2; assumption. }
                { exists sost; split; auto; findeq. }
              }
              { (* TODO: [SimMP] should be preserved by [removeMP];
                 * but just found that this preservation requires that no 
                 * internal messages remain when the target transaction ends.
                 * How can we ensure this property?
                 *)
                unfold distributeMsgs.
                do 2 rewrite app_nil_r.

                (* Maybe need to use the information that all the messages
                 * in implementation MP is about a single transaction?
                 * Given the atomicity...
                 *)
                admit.
              }
            }

            { admit. }

          * (* Now ready to synthesize (ordinary) [Rule]s 
             * based on the synthesized [PRule]s. *)
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

