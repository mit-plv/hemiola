Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics StepDet StepSeq.
Require Import Simulation Serial Predicate Synthesis SynthesisFacts.

Require Import SingleValue SingleValueSim.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section Impl.
  Variables extIdx1 extIdx2: nat.
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

  (** First, prove that the initial system is provided properly. *)
  Theorem impl0_ok: SynthOk spec (SimTrs SvmR) svmP impl0.
  Proof.
    repeat split.
    - admit.
    - repeat econstructor.
      apply noTrs_init.
    - admit.
  Admitted.
  
  Section SynStep.

    Ltac mv_rewriter :=
      repeat
        match goal with
        | [H: Some _ = M.find _ _ |- _] => apply eq_sym in H
        | [H: None = M.find _ _ |- _] => apply eq_sym in H
        | [H1: M.find ?m ?k1 = Some _, H2: M.find ?m ?k2 = Some _ |- _] =>
          rewrite H1 in H2; inv H2
        | [H1: M.find ?m ?k1 = Some _, H2: M.find ?m ?k2 = None |- _] =>
          rewrite H1 in H2; discriminate
        end.

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

    Ltac syn_step_init pimpl pimpl_ok :=
      econstructor;
      instantiate (1:= addPMsgsSys (_ :: _) pimpl);
      split; [|split]; (* [SynthOk] consist of 3 conditions. *)
      [|rewrite addPMsgsSys_init; apply pimpl_ok|].

    Ltac syn_step_sim pimpl_ok :=
      apply simulation_pmsgs_added;
      [apply pimpl_ok|];
      unfold Simulates; intros.

    Ltac inv_step_seq :=
      match goal with
      | [H: step_seq _ _ _ _ |- _] => inv H
      end.

    Ltac simulates_silent :=
      simpl; right; assumption.

    Ltac simulates_lbl_in validMsgMap_proven :=
      simpl;
      repeat
        match goal with
        | [H: context[isExternal (addPMsgsSys _ _)] |- _] =>
          rewrite addPMsgsSys_isExternal in H
        | [H: context[isInternal (addPMsgsSys _ _)] |- _] =>
          rewrite addPMsgsSys_isInternal in H
        | [H: context[isExternal (buildRawSys _)] |- _] =>
          rewrite buildRawSys_isExternal in H
        | [H: context[isInternal (buildRawSys _)] |- _] =>
          rewrite buildRawSys_isInternal in H
        | [ |- exists _ _, step_det _ ?sst1 _ _ /\ _] =>
          is_var sst1;
          let soss1 := fresh "soss1" in
          let smsgs1 := fresh "smsgs1" in
          let sts := fresh "sts" in
          destruct sst1 as [soss1 smsgs1 sts];
          eexists {| tst_oss := soss1;
                     tst_msgs := distributeMsg (toTMsgU _) smsgs1;
                     tst_tid := sts |};
          eexists (IlblIn (toTMsgU _))
        | [ |- _ /\ _] => split
        | [ |- _ <> emptyLabel] => discriminate
        | [ |- SimTrs _ _ _] => assumption
        | [ |- _ = ?t ] =>
          match type of t with
          | Label => reflexivity
          end
        | [ |- step_det _ _ _ _] => constructor
        | [H: isExternal _ (mid_from (msg_id _)) = true |-
           isExternal _ (mid_from (msg_id _)) = true] =>
          eapply validMsgMap_from_isExternal;
          [exact validMsgMap_proven|eassumption]
        | [H: isInternal _ (mid_to (msg_id _)) = true |-
           isInternal _ (mid_to (msg_id _)) = true] =>
          eapply validMsgMap_to_isInternal;
          [exact validMsgMap_proven|eassumption]
        end.

    Definition synTrs:
      { impl1: System & SynthOk spec (SimTrs SvmR) svmP impl1 }.
    Proof.
      syn_step_init impl0 impl0_ok.

      - (** serializability *) admit.
      - (** simulation *)
        syn_step_sim impl0_ok.
        inv_step_seq.

        + (** silent *)
          simulates_silent.
        + (** external message-in *)
          simulates_lbl_in svmMsgF_ValidMsgMap.
        + (** internal forwarding *)
          admit.
        + (** internal transaction started *)

          (* 1) Prove [In fpmsg (?a :: ?l)]: easy
           * 2) Synthesize ?a as the only [PMsg] accepting 
           *    the target external request.
           * 3) Synthesize ?l for any internal requests.
           * 4) Since [fpmsg] here is for the external request,
           *    we get fpmsg = ?a.
           * 5) Due to [pmsg_precond fpmsg os], now we can take
           *    the specific precondition for [os].
           * 6) By using [H: SimTrs ...] and the precondition of [os],
           *    we can guess the entire state invariant.
           *)
          admit.

    Admitted.
    
  End SynStep.

End Impl.

