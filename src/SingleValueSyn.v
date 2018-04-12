Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepT SemFacts.
Require Import Simulation Serial SerialFacts Invariant TrsSim.
Require Import PredMsg StepPred PredMsgFacts.
Require Import Synthesis SynthesisFacts Blocking.
Require Import Topology.

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
  Local Definition SvmSim := SvmSim extIdx1 implIndices.

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

  Definition SvmInvs :=
    BlockedInv /\i ValidTidState.

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
      | [H: SpecState _ _ |- _] =>
        let sost := fresh "sost" in
        destruct H as [sost [? ?]]
      | [H1: ImplStateMSI ?v1 ?tinds ?ioss, H2: ImplStateMSI ?v2 ?tinds ?ioss |- _] =>
        assert (v1 = v2) by eauto using impl_state_MSI_value_eq; subst v1
      | [H1: ImplStateMSI ?v1 ?tinds1 ?ioss, H2: ImplStateSI ?v2 ?tinds2 ?ioss |- _] =>
        assert (v1 = v2)
          by (eapply impl_state_MSI_restrict_SI_value_eq; eauto;
              [discriminate|subList_app_tac]
             );
        subst v1
      end.

  Ltac red_svm := red_SvmInvs; red_SvmSim.

  Ltac constr_sim_svm :=
    repeat
      (repeat (match goal with
               | [ |- SvmR _ _ _ ] => eexists; split
               | [H: ImplStateMSI _ _ ?ioss1 |- ImplStateMSI _ _ ?ioss2 ] =>
                 replace ioss2 with ioss1; eassumption
               | [ |- SpecState _ _ ] => eexists; split
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
           end; dest).

  Ltac constr_sim_mp :=
    repeat
      (try match goal with
           | [ |- context[distributeMsgs nil _] ] => unfold distributeMsgs
           | [ |- context[_ ++ nil] ] => rewrite app_nil_r
           | [ |- context[map _ (removeMP _ _)] ] =>
             erewrite mmap_removeMP by reflexivity
           | [ |- context[map _ (distributeMsgs _ _)] ] =>
             rewrite mmap_distributeMsgs
           | [ |- context[map _ (_ ++ _)] ] =>
             rewrite map_app

           | [H: context[map _ (removeMP _ _)] |- _] =>
             erewrite mmap_removeMP in H by reflexivity
           | [H: context[distributeMsgs nil _] |- _] => unfold distributeMsgs in H
           | [H: context[_ ++ nil] |- _] => rewrite app_nil_r in H
           | [H: context[map _ (distributeMsgs _ _)] |- _] =>
             rewrite mmap_distributeMsgs in H
           | [H: context[map _ (_ ++ _)] |- _] =>
             rewrite map_app in H

           | [ |- SimMP _ (removeMP _ _) (removeMP _ _) ] =>
             apply SimMP_ext_msg_immediate_out; auto
           | [ |- SimMP _ (removeMP _ _) (removeMP _ _) ] =>
             eapply SimMP_response_back_ext_out; eauto; repeat constructor
           | [ |- SimMP _ (distributeMsgs _ (removeMP ?emsg _)) _ ] =>
             let Hchk := fresh "Hchk" in
             assert (tmsg_info emsg = None) as Hchk by reflexivity; clear Hchk;
             eapply SimMP_ext_msg_rq_forwarding; try reflexivity; auto
           | [ |- SimMP _ ((removeMP ?emsg _) ++ _) _ ] =>
             let Hchk := fresh "Hchk" in
             assert (tmsg_info emsg = None) as Hchk by reflexivity; clear Hchk;
             eapply SimMP_ext_msg_rq_forwarding; try reflexivity; auto
                                                                    
           | [ |- SimMP _ (distributeMsgs [?rs] (removeMP ?rq _)) _ ] =>
             let Hchk := fresh "Hchk" in
             assert (tmsg_info rq = tmsg_info rs) as Hchk by reflexivity; clear Hchk;
             eapply SimMP_int_msg_immediate; try reflexivity; auto
           | [ |- SimMP _ ((removeMP ?rq _) ++ [?rs]) _ ] =>
             let Hchk := fresh "Hchk" in
             assert (tmsg_info rq = tmsg_info rs) as Hchk by reflexivity; clear Hchk;
             eapply SimMP_int_msg_immediate; try reflexivity; auto

           | [ |- TidLtMP _ _ ] => progress simpl
           | [H1: ValidTidState {| tst_msgs := ?msgs |}, H2: step_t _ _ _ _
              |- TidLtMP ?msgs _ ] =>
             eapply step_t_tid_next_TidLt in H2;
             [|eassumption|discriminate|discriminate
              |repeat constructor|repeat constructor];
             assumption
               
           | [ |- Forall (fun tmsg => tmsg_info tmsg = Some _) _ ] =>
             constructor; simpl; try reflexivity
           | [H: FirstMP ?imsgs _ |- FirstMP (map ?f ?imsgs) _ ] =>
             eapply mmap_FirstMP with (mmap:= f) in H; eauto
           end;
       cbn).
  
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
      | [H: step_t _ _ emptyRLabel _ |- _] => inv H
      end;
      (** constructions *)
      eexists; split; [econstructor|assumption].

    Ltac trs_simulates_case_in msgF sim :=
      (** instantiation *)
      unfold TrsSimIn; intros; simpl;
      match goal with
      | [H: context[RlblIn ?min] |- context[step_t _ ?ist1 _ _] ] =>
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
        | [H: step_t _ _ (RlblIn _) _ |- _] => inv H
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
        | [H: InvStep _ step_t _ |- _] => clear H
        end.

    Ltac reduce_invstep_pred :=
      repeat
        match goal with
        | [H: InvStep _ step_pred_t _ /\ _ |- _] => destruct H
        | [H: exists (_: PStateEx _) (_: PHistory TMsg) (_: PStateEx _), _ |- _] =>
          let pstx1 := fresh "pstx1" in
          let phst := fresh "phst" in
          let pstx2 := fresh "pstx2" in
          destruct H as [pstx1 [phst [pstx2 ?]]]; dest; subst
        | [H: forall _, _ = _ -> _ |- _] => specialize (H _ eq_refl)
        end.
    
    Ltac trs_simulates_atomic_to_steps_pred rqmid :=
      unfold TrsSimAtomic; intros;
      match goal with
      | [H: Atomic ?sys _ _ _ _ |- _] =>
        assert_later (ExtHandles sys [rqmid])
      end;
      repeat
        match goal with
        | [H: ExtHandles _ _ |- _] =>
          eapply atomic_extHandles in H; eauto
        | [H: In _ _ |- _] => Common.dest_in
        end;
      [match goal with
       | [H1: Atomic _ _ _ ?hst _, H2: steps step_t _ _ ?hst _ |- _] =>
         pose proof (atomic_history_pred_tinfo H1 H2)
       end;
       match goal with
       | [H: steps step_t (addRules _ (buildRawSys ?implTopo)) _ _ _ |- _] =>
         eapply atomic_steps_pred_ok
           with (psys:= addPRules _ (buildRawPSys _ implTopo)) in H;
         eauto; [clear_atomic_hyps; reduce_invstep_pred|]
       end|].

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
        | [H: InvStep _ _ tinv |- _] => clear H
        | [H: tinv _ |- _] => clear H
        | [H: tsim _ _ |- _] => clear H
        end.

    Ltac reduce_sim_steps_to_step tinv tsim :=
      match goal with
      | [H: steps ?stI _ _ _ _ |- context[steps ?stS _ _ _ _] ] =>
        eapply inv_simulation_steps
          with (stepS:= stS) (ginv:= tinv) (sim:= tsim) in H; eauto;
        [reduce_sim_steps_to_step_proof
        |reduce_sim_steps_to_step_clear tinv tsim]
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
      match goal with
      | [H: step_pred_t _ _ (PlblOuts ?orule _ _) _ |- _] =>
        is_var orule;
        let rule := fresh "rule" in destruct orule as [rule|]
      end;
      [|repeat
          match goal with
          | [H: step_pred_t _ _ _ _ |- _] => inv H
          | [H: step_pred0 _ _ (PlblOuts ?orule _ _) _ |- _] =>
            is_var orule;
            let rule := fresh "rule" in destruct orule as [rule|]
          | [H: step_pred0 _ _ (PlblOuts None _ _) _ |- _] => inv H; simpl in *
          | [H: step_t _ _ (RlblOuts None _ _) _ |- _] => inv H; simpl in *
          | [ |- _ \/ _ ] => right
          | [H1: pstx_st ?ist1 = pstx_st ?ist2, H2: pstx_pst ?ist1 = pstx_pst ?ist2 |- _] =>
            pose proof (PStateEx_ext _ _ H1 H2); subst; clear H1 H2
          | [H: ?t |- ?t] => assumption
          end].

    (** [PStack] (= [list PStackElt]), a job stack to figure out
     * which rule should be should be synthesized at the current point.
     *)
    
    Record PStackElt :=
      { pste_pmid: PMsgId TMsg;
        pste_prec: PRPrecond }.

    Definition dualOfPStackElt (chn: IdxT) (pste: PStackElt) :=
      {| pste_pmid := dualOfP (pste_pmid pste) chn;
         pste_prec := pste_prec pste |}.

    Ltac pstack_empty :=
      let stack := fresh "stack" in
      evar (stack: list (option PStackElt)).

    Ltac pstack_instance_fix st :=
      match st with
      | ?hd :: ?tl =>
        let tins := pstack_instance_fix tl in
        constr:(tins ++ hd :: nil)
      | _ => constr:(nil (A:= option PStackElt))
      end.

    Ltac pstack_instance :=
      match goal with
      | [st := ?stack : list (option PStackElt) |- _] =>
        let ins := pstack_instance_fix stack in
        let v := eval cbn in ins in v
      end.

    Ltac pstack_push e :=
      match goal with
      | [st := ?stack : list (option PStackElt) |- _] =>
        has_evar stack;
        instantiate (1:= Some e :: _) in (Value of st)
      end.

    Ltac pstack_push_pp pmid prec :=
      pstack_push {| pste_pmid := pmid;
                     pste_prec := prec |}.

    Ltac pstack_push_pmids pmids prec :=
      match pmids with
      | nil => idtac
      | ?pmid :: ?pmids' =>
        pstack_push_pp pmid prec;
        pstack_push_pmids pmids' prec
      end.

    Ltac pstack_push_a tid from to chn prec pred :=
      pstack_push {| pste_pmid :=
                       {| pmid_mid :=
                            {| mid_addr :=
                                 {| ma_from := from;
                                    ma_to := to;
                                    ma_chn := chn |};
                               mid_tid := tid |};
                          pmid_pred := pred
                       |};
                     pste_prec := prec |}.

    Fixpoint evalStackInstanceFix
             (st: list (option PStackElt)) (n: nat) :=
      match st with
      | nil => nil
      | None :: st' => evalStackInstanceFix st' (S n)
      | Some v :: st' =>
        match n with
        | O => v :: evalStackInstanceFix st' n
        | S n' => evalStackInstanceFix st' n'
        end
      end.

    Fixpoint evalStackInstance (st: list (option PStackElt)) :=
      evalStackInstanceFix st O.

    Ltac pstack_is_empty :=
      let ins := pstack_instance in
      let v := (eval cbn in (evalStackInstance ins)) in
      match v with
      | nil => idtac
      | _ :: _ => fail
      end.
    
    Ltac pstack_first :=
      let ins := pstack_instance in
      let v := (eval cbn in (evalStackInstance ins)) in
      match v with
      | ?v :: _ => v
      end.

    Fixpoint stackFirstN (n: nat) (st: list PStackElt) :=
      match n with
      | O => nil
      | S n' =>
        match st with
        | nil => nil
        | v :: st' => v :: stackFirstN n' st'
        end
      end.

    Ltac pstack_first_n n :=
      let ins := pstack_instance in
      let v := (eval cbn in (evalStackInstance ins)) in
      constr:(stackFirstN n v).

    Ltac pstack_pop :=
      match goal with
      | [st:= ?stack : list (option PStackElt) |- _] =>
        has_evar stack;
        instantiate (1:= None :: _) in (Value of st)
      end.

    Ltac pstack_clear :=
      match goal with
      | [st := ?stack : list (option PStackElt) |- _] =>
        has_evar stack;
        instantiate (1:= nil) in (Value of st);
        clear st
      end.

    (** End of [PStack]-related definitions *)

    (** [PRqRs], a record to track the target predicate messages
     * between a request-forwarding rule and its dual responses-back rule.
     *)

    Record PRqRs :=
      { prr_rq: PMsgId TMsg;
        prr_fwds: list (PMsgId TMsg)
      }.

    Ltac declare_prr :=
      let prr := fresh "prr" in
      evar (prr: PRqRs).

    Ltac get_prr :=
      match goal with
      | [p := ?prr : PRqRs |- _] => prr
      end.

    Ltac set_prr rq fwds :=
      match goal with
      | [p := ?prr : PRqRs |- _] =>
        is_evar prr;
        instantiate (1:= {| prr_rq := rq; prr_fwds := fwds |})
          in (Value of p)
      end.

    Ltac clear_prr :=
      match goal with
      | [p := _ : PRqRs |- _] => clear p
      end.

    Ltac pstack_push_from_prr_prec prec :=
      match goal with
      | [prr := {| prr_fwds := ?pmids |} |- _] =>
        pstack_push_pmids pmids prec
      end.

    Ltac pstack_push_from_prr_precs precs :=
      match precs with
      | nil => idtac
      | ?prec :: ?precs' =>
        pstack_push_from_prr_prec prec;
        pstack_push_from_prr_precs precs'
      end.

    Ltac pstack_push_from_prr precs :=
      match goal with
      | [p := _ : PRqRs |- _] =>
        cbn in p; pstack_push_from_prr_precs precs
      end.

    (** End of [PRqRs] *)

    Definition buildPRuleImmFromPStack (pste: PStackElt) (dchn: IdxT) :=
      PRuleImm (pste_pmid pste)
               (dualOfP (pste_pmid pste) dchn)
               (pste_prec pste).

    Definition buildPRuleRqFwdFromPStack (pste: PStackElt)
               (rqff: PMsgId TMsg -> list (PMsgId TMsg)) :=
      PRuleRqFwd (pste_pmid pste) (pste_prec pste) (rqff (pste_pmid pste)).

    Ltac set_prr_rqf :=
      match goal with
      | [H: context[buildPRuleRqFwdFromPStack
                      {| pste_pmid := ?rq |} ?rqff] |- _] =>
        set_prr rq (rqff rq)
      end.

    Ltac synth_prule_imm :=
      match goal with
      | [H: step_pred_t (addPRules ?rules _) _ _ _ |- _] =>
        is_evar rules; instantiate (1:= _ :: _);
        apply step_pred_rules_split_addPRules_1 in H;
        destruct H
      end.

    Ltac synth_prules_rqf_rsb :=
      match goal with
      | [H: step_pred_t (addPRules ?rules _) _ _ _ |- _] =>
        is_evar rules; instantiate (1:= _ :: _ :: _);
        declare_prr;
        apply step_pred_rules_split_addPRules_2 in H;
        destruct H as [|[|]]
      end.

    Ltac pstack_first_instantiate_imm_prule :=
      match goal with
      | [H: step_pred_t (addPRules [?rule] _) _ _ _ |- _] =>
        is_evar rule;
        let pfst := pstack_first in
        instantiate (1:= buildPRuleImmFromPStack pfst rsChn) in H
      end.

    Ltac pstack_first_instantiate_rqfwd_prule rqff :=
      match goal with
      | [H: step_pred_t (addPRules [?rule] _) _ _ _ |- _] =>
        is_evar rule;
        let pfst := pstack_first in
        instantiate (1:= buildPRuleRqFwdFromPStack pfst rqff) in H
      end.

    Ltac prr_instantiate_rsback_prule opred rsbf :=
      match goal with
      | [H: step_pred_t (addPRules [?rule] _) _ _ _ |- _] =>
        is_evar rule;
        let prr := get_prr in
        let rq := (eval cbn in (prr_rq prr)) in
        let rqf := (eval cbn in (prr_fwds prr)) in
        let rsb := (eval cbn in (dualOfP rq rsChn)) in
        let rss := (eval cbn in (map (fun pmid => dualOfP pmid rsChn) rqf)) in
        instantiate (1:= PRuleRsBack rss opred rsb rsbf) in H
      end.

    Ltac step_pred_invert_init :=
      repeat
        match goal with
        | [H: step_pred_t _ _ (PlblOuts (Some _) _ _) _ |- _] => inv H
        | [H: step_pred0 _ _ (PlblOuts (Some _) _ _) _ |- _] => inv H
        | [H: In _ (psys_rules _) |- _] => inv H; try discriminate
        | [H: In _ nil |- _] => inv H
        | [H: ?rule = _ |- _] =>
          match type of rule with
          | PRule _ => inv H
          end
        end.

    Ltac dest_pmsg_rq rq :=
      let rqfrom := fresh "rqfrom" in
      let rqto := fresh "rqto" in
      let rqchn := fresh "rqchn" in
      let rqtid := fresh "rqtid" in
      let rqpred := fresh "rqpred" in
      let rqval := fresh "rqval" in
      destruct rq as [[[[[rqfrom rqto rqchn] rqtid] rqval] rqinfo] rqpred].
      
    Ltac dest_pmsg_rs rs :=
      let rsfrom := fresh "rsfrom" in
      let rsto := fresh "rsto" in
      let rschn := fresh "rschn" in
      let rstid := fresh "rstid" in
      let rspred := fresh "rspred" in
      let rsval := fresh "rsval" in
      destruct rs as [[[[[rsfrom rsto rschn] rstid] rsval] rsinfo] rspred].

    Ltac dest_PStateEx pstx :=
      let toss := fresh "toss" in
      let tmsgs := fresh "tmsgs" in
      let tid := fresh "tid" in
      let pst := fresh "pst" in
      let str := fresh "str" in
      destruct pstx as [[toss tmsgs tid] pst str];
      red in str.

    Ltac step_pred_invert_dest_state :=
      repeat
        match goal with
        | [H: step_t _ (pstx_st ?ist1) _ (pstx_st ?ist2) |- _] =>
          is_var ist1; dest_PStateEx ist1;
          is_var ist2; dest_PStateEx ist2
        end.

    Ltac step_pred_invert_dest_pmsg origRq :=
      repeat
        match goal with
        (* For the original request *)
        | [H: origRq = msg_id ?rq |- _] =>
          let orqfrom := fresh "orqfrom" in
          let orqto := fresh "orqto" in
          let orqchn := fresh "orqchn" in
          let orqtid := fresh "orqtid" in
          let orqval := fresh "orqval" in
          destruct rq as [[[orqfrom orqto orqchn] orqtid] orqval];
          unfold origRq in H

        (* For immediate [PMsg]s *)
        | [H: DualPMsg ?rq ?rs |- _] =>
          is_var rq; dest_pmsg_rq rq;
          is_var rs; dest_pmsg_rs rs;
          cbn in *
        | [H: DualPMsg {| pmsg_omsg := _; pmsg_pred := _ |}
                       {| pmsg_omsg := _; pmsg_pred := _ |} |- _] => inv H
        | [H: DualMid {| mid_addr := _; mid_tid := _ |}
                      {| mid_addr := _; mid_tid := _ |} |- _] => inv H
        | [H: dualOf _ _ = {| mid_addr := _; mid_tid := _ |} |- _] => inv H

        (* For request-forwarding [PMsg]s *)
        | [H: {| mid_addr := _; mid_tid := _ |} = pmsg_mid ?rq |- _] =>
          dest_pmsg_rq rq
        | [H: ?lfwd :: ?lfwds = map (@pmsg_pmid _ _) ?rfwds |- _] =>
          let rqfwd := fresh "rqfwd" in
          let rqfwds := fresh "rqfwds" in
          destruct rfwds as [|rqfwd rqfwds]; [discriminate|];
          dest_pmsg_rq rqfwd;
          inv H
        | [H: nil = map (@pmsg_pmid _ _) ?rfwds |- _] =>
          destruct rfwds; [clear H|discriminate]

        (* For responses-back [PMsg]s *)
        | [H: dualOf {| mid_addr := _; mid_tid := _ |} _ = pmsg_mid ?rs |- _] =>
          dest_pmsg_rs rs
                            
        (* General *)
        | [H: {| pmid_mid := _; pmid_pred := _ |} = ?rhs |- _] => is_var rhs; inv H
        | [H: ?lhs = {| pmid_mid := _; pmid_pred := _ |} |- _] => is_var lhs; inv H
        | [H: {| pmid_mid := _; pmid_pred := _ |} =
              {| pmid_mid := _; pmid_pred := _ |} |- _] => inv H
        | [H: {| mid_addr := _; mid_tid := _ |} = ?rhs |- _] => is_var rhs; inv H
        | [H: ?lhs = {| mid_addr := _; mid_tid := _ |} |- _] => is_var lhs; inv H
        | [H: {| mid_addr := _; mid_tid := _ |} =
              {| mid_addr := _; mid_tid := _ |} |- _] => inv H
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
        | [H: LiftInv _ _ _ |- _] => red in H
        end.

    Ltac red_LiftSimL :=
      repeat
        match goal with
        | [H: LiftSimL _ _ _ _ |- _] => red in H
        end.

    Ltac red_pred :=
      repeat
        match goal with
        | [H: ?predos _ _ _ _ |- _] =>
          match type of predos with
          | PredOS => red in H
          end
        | [H: ?predmp _ _ |- _] =>
          match type of predmp with
          | PredMP _ => red in H
          end
        | [H: ?opred _ _ _ _ |- _] =>
          match type of opred with
          | OPred => red in H
          end
        | [H: ?rprec _ _ |- _] =>
          match type of rprec with
          | RPrecond => red in H
          end
        | [H: context[rsBackFDefault (?v :: nil) ?o] |- _] =>
          rewrite rsBackFDefault_singleton with (val:= v) (ost:= o) in *
        end.

    Ltac pred_ok_init custom_init :=
      custom_init;
      repeat
        match goal with
        | [H: OStateExistsP _ _ _ |- _] => red in H; dest
        | [H: OStateForallP _ _ _ |- _] => red in H; dest
        | [H: Forall _ _ |- _] => inv H
        end.

    Ltac pred_ok_forall :=
      Common.dest_in; ostatesfp_red_ex; hnf;
      repeat
        (repeat match goal with
                | [ |- OStateForallP _ _ _ ] => red
                | [ |- _ /\ _ ] => split
                | [ |- Forall _ _ ] => constructor
                end; ostatesfp_red_ex).

    Ltac pred_ok_exists :=
      repeat
        (repeat
           match goal with
           | [ |- exists _, _ ] => eexists
           | [ |- _ /\ _ ] => split
           | [ |- In ?idx _ ] =>
             tryif is_evar idx
             then idtac else (simpl; tauto)
           | [ |- OStateExistsP _ _ _ ] => red
           | [ |- ?m @[?k] = Some _ ] =>
             tryif is_evar k
             then idtac else (eassumption || findeq; fail)
           end;
         repeat
           match goal with
           | [ |- ?m @[?k] = Some _ ] => eassumption || findeq; fail
           | [H: In ?x _ |- In ?x _ ] =>
             eassumption || (clear -H; firstorder; fail)
           end).

    Ltac step_pred_invert_red origRq red_custom :=
      repeat (step_pred_invert_dest_state;
              step_pred_invert_dest_pmsg origRq;
              red_forall;
              red_ValidMsgsIn;
              red_LiftInv;
              red_LiftSimL;
              red_pred;
              clear_useless;
              red_custom;
              dest; cbn in *; subst).

    Ltac sim_spec_constr_silent_init :=
      repeat
        match goal with
        | [ |- _ \/ _ ] => right (* make a silent step for the spec *)
        end.

    Ltac sim_spec_constr_step_init ruleS :=
      repeat
        match goal with
        | [ |- context[step_t _ ?sst _ _] ] =>
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

    Ltac sim_spec_constr_step_t :=
      repeat
        (try match goal with
             | [ |- step_t _ _ _ _] => econstructor
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

    Ltac sim_spec_constr_sim_init :=
      repeat
        match goal with
        | [ |- LiftSimL _ _ _ _ ] => hnf
        | [ |- _ /\ _ ] => split; cbn
        end.
    
    Ltac sim_spec_constr_sim ssim msim :=
      sim_spec_constr_sim_init; [ssim|msim].

    Ltac sim_spec_constr_step srule ssim msim :=
      sim_spec_constr_step_init srule;
      sim_spec_constr_split;
      (* 1) Prove the external label equality first, *)
      [|sim_spec_constr_extLabel_eq|];
      (* 2) Prove the actual step relation, and *)
      [sim_spec_constr_step_t|];
      (* 3) Prove the preservation of simulation. *)
      sim_spec_constr_sim ssim msim.

    Ltac sim_spec_constr_silent constr_sim_os constr_sim_mp :=
      sim_spec_constr_silent_init;
      (* It suffices to prove simulation, due to the silent step. *)
      sim_spec_constr_sim constr_sim_os constr_sim_mp.

    (** FIXME:
     * - Some immediate rules do not generate external labels.
     * - Some responses-back rules do not generate external labels.
     *)
    
    (** Try to synthesize an immediate [PRule]. *)
    Ltac synth_imm_prule origRq srule red_sim constr_sim_os constr_sim_mp :=
      pstack_first_instantiate_imm_prule;
      pstack_pop;
      step_pred_invert_init;
      step_pred_invert_red origRq red_sim;
      sim_spec_constr_step srule constr_sim_os constr_sim_mp.

    (** Try to synthesize a request-forwarding [PRule]. *)
    Ltac synth_rqfwd_prule origRq rqff red_sim constr_sim_os constr_sim_mp :=
      pstack_first_instantiate_rqfwd_prule rqff;
      pstack_pop;
      set_prr_rqf;
      step_pred_invert_init;
      step_pred_invert_red origRq red_sim;
      sim_spec_constr_silent constr_sim_os constr_sim_mp.

    (** Try to synthesize a responses-back [PRule]. *)
    Ltac synth_rsback_prule origRq srule opred rsbf
         red_sim constr_sim_os constr_sim_mp precs :=
      prr_instantiate_rsback_prule opred rsbf;
      pstack_push_from_prr precs;
      clear_prr;
      step_pred_invert_init;
      step_pred_invert_red origRq red_sim;
      sim_spec_constr_step srule constr_sim_os constr_sim_mp.

    Ltac synth_done :=
      (tryif pstack_is_empty
        then idtac
        else idtac "Warning: the job stack is not empty!");
      repeat 
        match goal with
        | [H: step_pred_t _ _ _ _ |- _] =>
          instantiate (1:= nil) in H;
          exfalso; clear -H; inv H
        | [H: step_t _ _ _ _ |- _] => inv H
        | [H: In _ (sys_rules _) |- _] => destruct H
        end.
    
    Definition svmTrsIdx0: TrsId := SvmGetE.
    Definition svmTrsRq0: MsgId :=
      {| mid_addr := {| ma_from := extIdx1;
                        ma_to := child1Idx;
                        ma_chn := rqChn |};
         mid_tid := svmTrsIdx0 |}.
    
    Definition svmSynTrs0:
      { impl1: System & SynthOk spec SvmSim SvmInvs svmP impl1 }.
    Proof.
      syn_step_init impl0 impl0_ok.

      - (** Simulation and preservation of global invariants. *)
        trs_sim_init impl0_ok.

        + (** [TrsSimulates] for newly added [Rule]s *)          
          trs_simulates_trivial svmMsgF SvmSim.

          (** [TrsSimAtomic]: [TrsSimulates] for [Atomic] steps. *)
          (* Now convert the target [Atomic] [steps_t] into [steps_pred].
           * We will have two subgoals, one for synthesizing predicate rules
           * and the other for synthesizing actual executable rules, using
           * already-synthesized predicate rules.
           *)
          trs_simulates_atomic_to_steps_pred svmTrsRq0.

          * (** Synthesis of [PRules]. *)

            (* Reduce steps-to-steps to a step-to-step proof. *)
            inv_lift SvmInvs.
            sim_liftL SvmSim.
            reduce_sim_steps_to_step
              (LiftInv (pstx_st (stR:= PTStateR)) SvmInvs)
              (LiftSimL (pstx_st (stR:= PTStateR)) SvmSim).

            (** Prove [InvSim], a (step-)simulation from [step_pred] to [step_t]: *)
            inv_sim_init step_pred_t.

            (* Prove simulation for silent steps, which is trivial. *)
            sim_pred_silent.

            (* Prove simulation for internal steps, 
             * and synthesize predicate rules simultaneously.
             *)

            (* A job stack will be used to track which rules
             * should be synthesized now. *)
            pstack_empty.

            (* Add initial requests. *)
            pstack_push_a svmTrsIdx0 extIdx1 child1Idx rqChn ImplOStatusI
                          {| pred_os := PredGet implIndices; pred_mp := NoMsgsTs ts |}.
            pstack_push_a svmTrsIdx0 extIdx1 child1Idx rqChn ImplOStatusS
                          {| pred_os := PredGet implIndices; pred_mp := NoMsgsTs ts |}.
            pstack_push_a svmTrsIdx0 extIdx1 child1Idx rqChn ImplOStatusM
                          {| pred_os := PredGet implIndices; pred_mp := NoMsgsTs ts |}.

            (** Dequeue the first element of [list PStackElt] and
             * try to synthesize a [PRule]. Always try to synthesize
             * an immediate rule [PRuleImm] first.
             *)
            (* Should succeed when {C1.st = M} *)
            try (synth_prule_imm;
                 [synth_imm_prule svmTrsRq0 (specGetReq extIdx1 extIdx1)
                                  red_svm constr_sim_svm constr_sim_mp|]).

            (* Should succeed when {C1.st = S} *)
            try (synth_prule_imm;
                 [synth_imm_prule svmTrsRq0 (specGetReq extIdx1 extIdx1)
                                  red_svm constr_sim_svm constr_sim_mp|]).

            (* Should fail when {C1.st = I}:
             * TODO: need an Ltac to heuristically check that it is feasible
             * to have the next [OState] using a target rule being synthesized 
             * now.
             *)
            try (synth_prule_imm;
                 [fail (* TODO: [synth_imm_prule] should fail here. *)|]).

            (** If synthesizing the immediate rule fails,
             * synthesize a request-forwarding rule and 
             * the dual response-back rule.
             *)
            synth_prules_rqf_rsb; [| |clear_prr].
            { synth_rqfwd_prule
                svmTrsRq0 (getRqFwdF implTopo)
                red_svm constr_sim_svm constr_sim_mp.
            }
            { synth_rsback_prule
                svmTrsRq0 (specGetReq extIdx1 extIdx1) OPredGetS rsBackFDefault
                red_svm constr_sim_svm constr_sim_mp
                [ImplOStatusI; ImplOStatusS; ImplOStatusM].
            }

            synth_prule_imm.
            { pstack_first_instantiate_imm_prule.
              pstack_pop.
              step_pred_invert_init.
              step_pred_invert_red svmTrsRq0 red_svm.
              sim_spec_constr_silent_init.
              sim_spec_constr_sim_init.
              { constr_sim_svm.
                right; split.
                { pred_ok_init svm_pred_ok_init; pred_ok_exists. }
                { pred_ok_init svm_pred_ok_init; pred_ok_forall. }
              }
              { constr_sim_mp. }
            }

            synth_prule_imm.
            { pstack_first_instantiate_imm_prule.
              pstack_pop.
              step_pred_invert_init.
              step_pred_invert_red svmTrsRq0 red_svm.
              sim_spec_constr_silent_init.
              sim_spec_constr_sim_init.
              { constr_sim_svm.
                right; split.
                { pred_ok_init svm_pred_ok_init; pred_ok_exists. }
                { pred_ok_init svm_pred_ok_init; pred_ok_forall. }
              }
              { constr_sim_mp. }
            }

            synth_prules_rqf_rsb; [| |clear_prr].
            { pstack_first_instantiate_rqfwd_prule (getRqFwdF implTopo).
              pstack_pop.
              set_prr_rqf.
              step_pred_invert_init.
              step_pred_invert_red svmSynRq0 red_svm.
              sim_spec_constr_silent constr_sim_svm constr_sim_mp.
            }
            { prr_instantiate_rsback_prule OPredGetS rsBackFDefault.
              pstack_push_from_prr [ImplOStatusI; ImplOStatusS; ImplOStatusM].
              clear_prr.
              step_pred_invert_init.
              step_pred_invert_red svmSynRq0 red_svm.
              sim_spec_constr_silent_init.
              sim_spec_constr_sim_init.
              { constr_sim_svm.
                right; split.
                { pred_ok_init svm_pred_ok_init; pred_ok_exists. }
                { pred_ok_init svm_pred_ok_init; pred_ok_forall. }
              }
              { constr_sim_mp. }
            }

            synth_prule_imm.
            { pstack_first_instantiate_imm_prule.
              pstack_pop.
              step_pred_invert_init.
              step_pred_invert_red svmTrsRq0 red_svm.
              sim_spec_constr_silent_init.
              sim_spec_constr_sim_init.
              { constr_sim_svm.
                right; split.
                { pred_ok_init svm_pred_ok_init; pred_ok_exists. }
                { pred_ok_init svm_pred_ok_init; pred_ok_forall. }
              }
              { constr_sim_mp. }
            }
            
            synth_prule_imm.
            { pstack_first_instantiate_imm_prule.
              pstack_pop.
              step_pred_invert_init.
              step_pred_invert_red svmTrsRq0 red_svm.
              sim_spec_constr_silent_init.
              sim_spec_constr_sim_init.
              { constr_sim_svm.
                right; split.
                { pred_ok_init svm_pred_ok_init; pred_ok_exists. }
                { pred_ok_init svm_pred_ok_init; pred_ok_forall. }
              }
              { constr_sim_mp. }
            }

            try (synth_prule_imm; [fail|]).
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
    
  End SynStep.

End Impl.

