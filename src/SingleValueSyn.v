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

    Local Definition targetObjIdx := child1Idx.
    Local Definition targetTrsIdx := 0.

    Ltac get_target_trs impl oidx tidx :=
      let oobj := (eval cbn in (nth_error (sys_objs impl) oidx)) in
      match oobj with
      | Some ?obj =>
        let otrs := (eval cbn in (nth_error (obj_trs obj) tidx)) in
        match otrs with
        | Some ?trs => exact trs
        end
      end.

    Ltac cbner t := let ct := (eval cbn in t) in exact ct.

    Ltac get_precond trs :=
      cbner (pmsg_precond trs).
    
    Local Definition targetTrs: PMsg :=
      ltac:(get_target_trs impl0 targetObjIdx targetTrsIdx).

    Local Definition targetMid: MsgId := pmsg_mid targetTrs.
    Local Definition targetSpecMid := svmMsgIdF extIdx1 extIdx2 targetMid.
    Local Definition targetPrec: PreCond := ltac:(get_precond targetTrs).

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

    Ltac find_new_prec cprec invs :=
      match invs with
      | nil => fail
      | ?inv :: ?invs' =>
        tryif (inv_not_compatible cprec inv)
        then (exact inv)
        else find_new_prec cprec invs'
      end.

    Local Definition newPrec: PreCond :=
      ltac:(let tgt := (eval hnf in targetPrec) in
            let invs := (eval hnf in svmImplChild1Inv) in
            find_new_prec tgt invs).

    Ltac syn_step_init pimpl pimpl_ok :=
      econstructor;
      instantiate (1:= addPMsgsSys _ pimpl);
      split; [|split]; (* [SynthOk] consist of 3 conditions. *)
      [|rewrite addPMsgsSys_init; apply pimpl_ok|].

    Ltac syn_step_sim pimpl_ok :=
      apply simulation_pmsgs_added;
      [apply pimpl_ok|].

    Definition synTrs:
      { impl1: System & SynthOk spec (SimTrs SvmR) svmP impl1 }.
    Proof.
      syn_step_init impl0 impl0_ok.

      - (* serializability *) admit.
      - (* simulation *)
        syn_step_sim impl0_ok.
        unfold Simulates; intros.
    Admitted.
    
  End SynStep.

End Impl.

