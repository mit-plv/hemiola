Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepT SemFacts.
Require Import Simulation Serial SerialFacts Invariant TrsSim.
Require Import PredMsg StepPred PredMsgFacts.
Require Import Synthesis SynthesisFacts SynthesisTactics.
Require Import Topology.

Require Import SingleValue SingleValueSim.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section Impl.
  Definition extIdx1 := 3.
  Definition extIdx2 := 4.

  Local Definition spec := spec extIdx1 extIdx2.
  Local Definition svmMsgIdF := svmMsgIdF extIdx1.
  Local Definition svmMsgF := svmMsgF extIdx1.
  Local Definition svmP := svmP extIdx1.
  Local Definition SvmSim := SvmSim extIdx1 implIndices.

  (*! Customized reduction and construction tactics *)

  Ltac red_SvmInvs :=
    repeat 
      match goal with
      | [H: SvmInvs _ |- _] => destruct H
      | [H: (_ /\i _) _ |- _] => destruct H
      end.

  Ltac red_SvmSim :=
    repeat
      match goal with
      | [H: SvmSim _ _ |- _] => destruct H
      | [H: SvmR _ _ _ |- _] =>
        let cv := fresh "cv" in
        destruct H as [cv [? ?]]
      | [H: SvmSpecState _ _ |- _] =>
        let sost := fresh "sost" in
        destruct H as [sost [? ?]]
      | [H: SvmSpecORqs _ |- _] =>
        let sorq := fresh "sorq" in
        destruct H as [sorq ?]
      | [H1: ImplStateMSI ?v1 ?tinds ?ioss, H2: ImplStateMSI ?v2 ?tinds ?ioss |- _] =>
        assert (v1 = v2) by eauto using impl_state_MSI_value_eq; subst v1
      | [H1: ImplStateMSI ?v1 ?tinds1 ?ioss, H2: ImplStateSI ?v2 ?tinds2 ?ioss |- _] =>
        assert (v1 = v2)
          by (eapply impl_state_MSI_restrict_SI_value_eq; eauto;
              [discriminate|subList_app_tac]
             ); subst v1
      end.

  Ltac red_svm := red_SvmInvs; red_SvmSim.

  Ltac constr_sim_svm :=
    repeat
      (repeat (match goal with
               | [ |- SvmR _ _ _ ] => eexists; split
               | [H: ImplStateMSI _ _ ?ioss1 |- ImplStateMSI _ _ ?ioss2 ] =>
                 replace ioss2 with ioss1; eassumption
               | [ |- SvmSpecState _ _ ] => eexists; split
               | [ |- SvmSpecORqs _ ] => eexists
               end);
       try (findeq; fail); try reflexivity; try eassumption
      ).

  Ltac svm_pred_ok_init :=
    repeat
      (try match goal with
           | [H: ImplStateMSI _ _ _ |- _] => destruct H
           | [H: ImplStateMI _ _ _ |- _] => hnf in H
           | [H: ImplStateSI _ _ _ |- _] => hnf in H
           | [H: ImplStateI _ _ |- _] => hnf in H
           | [ |- context[ImplStateMSI _ _ _] ] => unfold ImplStateMSI
           | [ |- context[ImplStateMI _ _ _] ] => unfold ImplStateMI
           | [ |- context[ImplStateSI _ _ _] ] => unfold ImplStateSI
           | [ |- context[ImplStateI _ _] ] => unfold ImplStateI
           end; dest).

  (*! Correctness of the initial system *)
  
  Theorem impl0_ok: SynthOk spec SvmSim SvmInvs svmP impl0.
  Proof.
    synthOk_init.
    - apply SvmSim_init.
    - apply SvmInvs_init.
    - split.
      + apply TrsSimulates_no_rules.
        * apply svmMsgF_ValidMsgMap.
        * hnf; intros.
          destruct H; destruct H0.
          simpl in *.
          repeat split; simpl; auto.
          apply SimMP_ext_msg_in; auto.
        * reflexivity.
      + (* invariants *) admit.
    - (* serializability *) admit.
  Admitted.

  (*! Synthesis to build a single transaction  *)

  Definition svmTrsIdx0: TrsId := SvmGetE.
  Definition svmTrsRq0: MsgId :=
    {| mid_addr := {| ma_from := extIdx1;
                      ma_to := child1Idx;
                      ma_chn := rqChn |};
       mid_tid := svmTrsIdx0 |}.
  
  Definition svmSynTrs0:
    { impl1: System | SynthOk spec SvmSim SvmInvs svmP impl1 }.
  Proof.
    syn_step_init impl0 impl0_ok.

    - (** Simulation and preservation of global invariants. *)
      trs_sim_init impl0_ok.

      + (** [TrsSimulates] for newly added [Rule]s *)
        trs_simulates_trivial svmMsgF svmMsgF_ValidMsgMap SvmSim.

        (** [TrsSimAtomic]: [TrsSimulates] for [Atomic] steps. *)
        (* Now convert the target [Atomic] [steps_t] into [steps_pred].
         * We will have two subgoals, one for synthesizing predicate rules
         * and the other for synthesizing actual executable rules, using
         * already-synthesized predicate rules.
         *)
        trs_simulates_atomic_to_steps_pred svmTrsRq0.

        * (** Synthesis of [PRule]s. *)

          (* Reduce steps-to-steps to a step-to-step proof. *)
          inv_lift SvmInvs.
          sim_liftL SvmSim.
          reduce_sim_steps_to_step
            (LiftInv (pstx_st (stR:= PTStateR)) SvmInvs)
            (LiftSimL (pstx_st (stR:= PTStateR)) SvmSim).

          (** Prove [InvSim], a (step-)simulation 
           * from [step_pred] to [step_t]: 
           *)
          inv_sim_init step_pred_t.

          (* Prove simulation for silent steps, which is trivial. *)
          sim_pred_silent.

          (** Synthesize [PRule]s for internal steps (by predicate messages)
           * and prove corresponding simulation simultaneously
           *)

          (* A job stack is used to track which rules should be 
           * synthesized now. 
           *)
          pstack_empty.

          (* Add initial requests. *)
          pstack_push_a svmTrsIdx0 extIdx1 child1Idx rqChn ImplOStatusI
                        {| pred_os := PredGet implIndices;
                           pred_mp := NoMsgsTs ts |}.
          pstack_push_a svmTrsIdx0 extIdx1 child1Idx rqChn ImplOStatusS
                        {| pred_os := PredGet implIndices;
                           pred_mp := NoMsgsTs ts |}.
          pstack_push_a svmTrsIdx0 extIdx1 child1Idx rqChn ImplOStatusM
                        {| pred_os := PredGet implIndices;
                           pred_mp := NoMsgsTs ts |}.

          (* Dequeue the first element of the job stack and 
           * try to synthesize a [PRule].
           * Always try to synthesize an immediate rule [PRuleImm] first.
           *)
          
          (* Should succeed when [C1.status = M]. *)
          synth_prule_one
            ltac:(synth_imm_prule_ext
                    svmTrsRq0 (specGetReq extIdx1 extIdx1)
                    red_svm constr_sim_svm constr_sim_mp
                    nothing nothing).

          (* Should succeed when [C1.status = S]. *)
          synth_prule_one
            ltac:(synth_imm_prule_ext
                    svmTrsRq0 (specGetReq extIdx1 extIdx1)
                    red_svm constr_sim_svm constr_sim_mp
                    nothing nothing).
          
          (* Should _fail_ when [C1.status = I].
           * TODO: need an Ltac to heuristically check that there is no local
           * state transition that satisfies the request predicate and the
           * given local precondition.
           *)
          try (synth_prule_one; [fail|]).

          (* If synthesizing the immediate rule fails, try to synthesize 
           * a request-forwarding rule and the corresponding response-back rule.
           *)
          synth_prule_two
            ltac:(synth_rqfwd_prule
                    svmTrsRq0 (getRqFwdF implTopo)
                    red_svm constr_sim_svm constr_sim_mp nothing nothing)
            ltac:(synth_rsback_prule_ext
                    svmTrsRq0 (specGetReq extIdx1 extIdx1) OPredGetS rsBackFDefault
                    red_svm constr_sim_svm constr_sim_mp nothing nothing
                    [ImplOStatusI; ImplOStatusS; ImplOStatusM]).

          (* The status of the job stack says now it's time to synthesize
           * rules for the parent.
           *)

          (* Should be able to synthesize an immediate rule
           * when [P.status = M]. *)
          synth_prule_one
            ltac:(synth_imm_prule_int
                    svmTrsRq0 red_svm constr_sim_svm constr_sim_mp
                    ltac:(pred_ok svm_pred_ok_init) nothing).

          (* Should succeed when [P.status = S]. *)
          synth_prule_one
            ltac:(synth_imm_prule_int
                    svmTrsRq0 red_svm constr_sim_svm constr_sim_mp
                    ltac:(pred_ok svm_pred_ok_init) nothing).

          (* Should fail when [P.status = I]. *)
          try (synth_prule_one; [fail|]).
          
          (* Try to synthesize a request-forwarding rule and 
           * the corresponding response-back rule.
           *)
          synth_prule_two
            ltac:(synth_rqfwd_prule
                    svmTrsRq0 (getRqFwdF implTopo)
                    red_svm constr_sim_svm constr_sim_mp nothing nothing)
            ltac:(synth_rsback_prule_int
                    svmTrsRq0 OPredGetS rsBackFDefault
                    red_svm constr_sim_svm constr_sim_mp
                    ltac:(pred_ok svm_pred_ok_init) nothing
                    [ImplOStatusI; ImplOStatusS; ImplOStatusM]).

          (* Time for child2 *)
          
          (* Should succeed when [C2.status = M]. *)
          synth_prule_one
            ltac:(synth_imm_prule_int
                    svmTrsRq0 red_svm constr_sim_svm constr_sim_mp
                    ltac:(pred_ok svm_pred_ok_init) nothing).

          (* Should succeed when [C2.status = S]. *)
          synth_prule_one
            ltac:(synth_imm_prule_int
                    svmTrsRq0 red_svm constr_sim_svm constr_sim_mp
                    ltac:(pred_ok svm_pred_ok_init) nothing).

          (* Should fail when [C2.status = I].
           * TODO: here request-forwarding should fail as well, 
           * since there's nowhere to forward the message.
           *)
          try (synth_prule_one; [fail|]).
          try (synth_prule_two; [fail| |]).
          pstack_pop.

          synth_done.
          
        * (* Now ready to synthesize (ordinary) [Rule]s
           * based on the synthesized [PRule]s. *)
          admit.

        * (* Additionally need to show some static properties about 
           * the synthesized [Rule]s. *)
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

End Impl.

Close Scope list.
Close Scope fmap.

