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

    Ltac get_target_trs impl oidx tidx pname :=
      let oobj := (eval cbn in (nth_error (sys_objs impl) oidx)) in
      match oobj with
      | Some ?obj =>
        let otrs := (eval cbn in (nth_error (obj_trs obj) tidx)) in
        match otrs with
        | Some ?trs => pose trs as pname
        end
      end.

    Ltac cbner t tn := let ct := (eval cbn in t) in pose ct as tn.
    Ltac hnfer t tn := let ht := (eval hnf in t) in pose ht as tn.

    Ltac get_precond trs pname :=
      cbner (pmsg_precond trs) pname.

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

    (* If it succeeds, then provably [inv1] and [inv2] are not compatible 
     * for all state.
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
      instantiate (1:= addPMsgsSys _ pimpl);
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

    Definition synTrs:
      { impl1: System & SynthOk spec (SimTrs SvmR) svmP impl1 }.
    Proof.
      syn_step_init impl0 impl0_ok.

      - (* serializability *) admit.
      - (* simulation *)
        syn_step_sim impl0_ok.
        inv_step_seq.

        + (* silent *) simulates_silent.
        + (* external message-in *)
          (** TODO: Ltac simulates_lbl_in := (... below ...) *)
          rewrite addPMsgsSys_isExternal, buildRawSys_isExternal in H1.
          rewrite addPMsgsSys_isInternal, buildRawSys_isInternal in H2.
          simpl; destruct sst1 as [soss1 smsgs1 sts].
          eexists {| tst_oss := soss1;
                     tst_msgs := distributeMsg (toTMsgU _) smsgs1;
                     tst_tid := sts |}.
          eexists (IlblIn (toTMsgU _)).
          repeat split;
            [|discriminate (* IlblIn _ <> emptyLabel *)
             |assumption (* States don't change 
                          * when external messages are added *)
            ].
          econstructor.
          * pose proof (validMsgMap_from_isExternal _ _ _ svmMsgF_ValidMsgMap).
            rewrite <-H0; auto.
          * pose proof svmMsgF_ValidMsgMap.
            specialize (H0 emsg); dest.
            rewrite <-H3; auto.

        + (* internal transaction started *)
          admit.

        + (* internal forwarding *)
          admit.

    Admitted.
    
  End SynStep.

End Impl.

