Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet SemFacts.
Require Import Simulation TrsSim Serial Predicate Synthesis SynthesisFacts.

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
        let otrs := (eval cbn in (nth_error (obj_trs obj) tidx)) in
        match otrs with
        | Some ?trs => pose trs as pname
        end
      end.

    Ltac cbner t tn := let ct := (eval cbn in t) in pose ct as tn.
    Ltac hnfer t tn := let ht := (eval hnf in t) in pose ht as tn.

    Ltac get_pmsg_from trs pname :=
      cbner (mid_from (pmsg_mid trs)) pname.
    Ltac get_pmsg_precond trs pname :=
      cbner (pmsg_precond trs) pname.

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

    Section Internalize.
      Variable sys: System.
      
      Definition makeIdxInternal (idx: IdxT): IdxT :=
        if isInternal sys idx
        then idx
        else (hd 0 (map obj_idx (sys_objs sys))).
      
      Definition makeMsgIdInternal (mid: MsgId): MsgId :=
        {| mid_type := mid_type mid;
           mid_from := makeIdxInternal (mid_from mid);
           mid_to := mid_to mid;
           mid_chn := mid_chn mid
        |}.
      
      Definition makePMsgInternal (pmsg: PMsg): PMsg :=
        {| pmsg_mid := makeMsgIdInternal (pmsg_mid pmsg);
           pmsg_precond := pmsg_precond pmsg;
           pmsg_outs := pmsg_outs pmsg;
           pmsg_postcond := pmsg_postcond pmsg
        |}.

      Lemma makePMsgInternal_in_internal:
        sys_objs sys <> nil ->
        forall tpmsg pmsgs,
          In tpmsg (map makePMsgInternal pmsgs) ->
          isInternal sys (mid_from (pmsg_mid tpmsg)) = true.
      Proof.
        induction pmsgs as [|pmsg pmsgs]; simpl; intros; [intuition idtac|].
        destruct H0; subst; auto.
        unfold makePMsgInternal; simpl.
        unfold makeIdxInternal.
        remember (isInternal sys (mid_from (pmsg_mid pmsg))) as ii.
        find_if_inside; auto.
        unfold isInternal, indicesOf.
        destruct (sys_objs sys) as [|hobj tobs]; [elim H; reflexivity|].
        simpl; destruct (_ ==n _); auto.
      Qed.

    End Internalize.

    Ltac syn_step_init pimpl pimpl_ok :=
      econstructor;
      (* instantiate (1:= addPMsgsSys (_ :: map (makePMsgInternal pimpl) _) pimpl); *)
      instantiate (1:= addPMsgsSys _ pimpl);
      split; [|split]; (* [SynthOk] consist of 3 conditions. *)
      [rewrite addPMsgsSys_init; apply pimpl_ok| |].

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
        | [ |- ?R _ _] =>
          match type of R with
          | (TState -> TState -> Prop) => assumption
          end
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

    Definition svmTrsIdx0 := 0.
    Definition svmTargetOIdx0 := child1Idx.
    Definition svmTargetPMsgIdx0 := 0.

    Definition svmSynTrs0:
      { impl1: System & SynthOk spec SvmSim svmP impl1 }.
    Proof.
      get_target_trs impl0 svmTargetOIdx0 svmTargetPMsgIdx0 ttrs.
      get_pmsg_from ttrs tfrom.
      get_pmsg_precond ttrs tprec.
      find_new_prec tprec svmImplChild1Inv nprec.

      syn_step_init impl0 impl0_ok.

      - (** simulation *)
        apply trsSimulates_pmsgs_added.
        + apply impl0_ok.
        + repeat constructor.
          * unfold mtPreservingPMsg; cbn; intros.
            destruct ((ost_st pre)@[valueIdx]); simpl.
            { repeat constructor. }
            { repeat constructor. }
          * unfold mtPreservingPMsg; cbn; intros.
            destruct ((ost_st pre)@[valueIdx]); simpl.
            { repeat constructor. }
            { repeat constructor. }


        + (** simulation for newly added [PMsg]s *)
          unfold TrsSimulates; intros.
          admit.
        + admit.
        + admit.
            
      - (** serializability *)
        admit.
        
    Admitted.
    
  End SynStep.

End Impl.

