Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet SemFacts.
Require Import Simulation Serial SerialFacts TrsInv TrsSim.
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

  Lemma svmMsgF_ValidMsgMap:
    ValidMsgMap svmMsgF impl0 spec.
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

  Theorem impl0_ok: SynthOk spec SvmSim SvmInv svmP impl0.
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
      split; [|split; [|split]]; (* [SynthOk] consist of 5 conditions. *)
      try (rewrite addRules_init; apply pimpl_ok; fail).

    Ltac trs_sim_init pimpl_ok :=
      apply trsSimulates_trsInvHolds_rules_added;
      [apply pimpl_ok|apply pimpl_ok|repeat constructor| | | |].

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
      (** some inversions *)
      repeat
        match goal with
        | [H: step_det _ _ (RlblIn _) _ |- _] => inv H
        | [H: sim _ _ |- _] => inv H
        end;
      (** construction *)
      repeat split;
      [|assumption (* simulation relation should be maintained *)
       |simpl; apply SimMP_ext_msg_in; auto];
      repeat econstructor;
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
      [admit (* TODO: the silent case; should be able to prove it to force that
              * synthesized rules never introduce silent steps.
              *)
      |trs_simulates_case_in msgF sim
      |].

    Definition svmTrsIdx0: TrsId := SvmGetE.
    (* Definition svmTrsRqIn0: MsgId := *)
    (*   {| mid_addr := {| ma_from := extIdx1; *)
    (*                     ma_to := child1Idx; *)
    (*                     ma_chn := rqChn |}; *)
    (*      mid_tid := svmTrsIdx0 |}. *)
    (* Definition svmTrsSpecRule0 := specGetReq extIdx1 extIdx2 specChn1. *)
    
    Definition svmSynTrs0:
      { impl1: System & SynthOk spec SvmSim SvmInv svmP impl1 }.
    Proof.
      syn_step_init impl0 impl0_ok.

      - (** Simulation and preservation of global invariants. *)
        trs_sim_init impl0_ok.

        + (** [TrsSimulates] for newly added [Rule]s *)
          trs_simulates_trivial svmMsgF SvmSim.

          (** [TrsSimAtomic]: [TrsSimulates] for [Atomic] steps *)
          unfold TrsSimAtomic; intros.
          pose proof (atomic_hst_tinfo H H2).

          (* Convert an [Atomic] [steps_det] into [steps_pred]. *)
          eapply steps_pred_ok
            with (psys:= addPRules _ (buildRawPSys impl0)) in H2; eauto.

          * (* In this subgoal it suffices to synthesize [PRules]. *)
            clear H. (* Atomicity is no longer needed. *)
            destruct H2 as [pst1 [phst [pst2 [? [? [? ?]]]]]].
            subst.

            (* Reduction to the simulation proof. *)
            assert (Forall (fun lbl =>
                              match lbl with
                              | PlblIn _ => False
                              | PlblOuts _ _ _ => True
                              end) phst).
            { clear -H3; induction phst; simpl; intros; [constructor|].
              inv H3; constructor; auto.
              destruct a; auto.
            }
            clear H3.

            eapply label_inv_simulation_steps
              with (stepS:= step_det) (sim:= LiftSimL SvmSim (pToTState ts rq))
              in H5; eauto.
            { destruct H5 as [sst2 [shst [? [? ?]]]].
              exists sst2, shst.
              split; [|split]; eauto.

              rewrite addPRules_behaviorOf in H3.
              rewrite addRules_behaviorOf.
              rewrite <-buildRawPSys_pToSystem_buildRawSys.
              rewrite <-pToTHistory_behaviorOf.
              eassumption.
            }

            (* For each case of [step_pred], *)
            clear H5. (* [steps_pred] is no longer needed. *)
            unfold LInvSim; intros.
            clear mouts.
            destruct ilbl as [|orule mins mouts]; [intuition idtac|clear H3].
            destruct orule as [rule|]; [|inv H4; simpl; right; auto].
            
            clear H phst.

            (* Use a stack to track which rules should be synthesized now. *)
            Record PStackElt :=
              { pste_rr: RqRs;
                pste_pmid: PMsgId;
                pste_prec: PRPrecond }.

            Ltac pstack_empty :=
              set (nil (A:= PStackElt)) as stack.

            pstack_empty.

            (* Add initial requests *)

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

            pstack_enq svmTrsIdx0 Rq extIdx1 child1Idx rqChn
                       ImplOStatusM getPred.
            pstack_enq svmTrsIdx0 Rq extIdx1 child1Idx rqChn
                       ImplOStatusS getPred.
            pstack_enq svmTrsIdx0 Rq extIdx1 child1Idx rqChn
                       ImplOStatusI getPred.

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

            Definition buildPRuleImm (pste: PStackElt) :=
              PRuleImm (pste_pmid pste) (pste_prec pste).

            Ltac synth_prule :=
              match goal with
              | [H: step_pred (addPRules ?rules _) _ _ _ |- _] =>
                is_evar rules; instantiate (1:= _ :: _);
                apply step_pred_rules_split_addPRules in H;
                destruct H
              end.

            admit.

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

