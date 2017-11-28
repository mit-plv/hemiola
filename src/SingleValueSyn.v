Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet StepSeq SemFacts.
Require Import Simulation Serial Predicate Synthesis SynthesisFacts.

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

  Theorem impl0_ok: SynthOk spec (SimTrs SvmR) svmP impl0.
  Proof.
    repeat split.
    - (* serializability *) admit.
    - econstructor.
      + apply simEquiv_refl.
      + repeat econstructor.
    - (* simulation *) admit.
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
      instantiate (1:= addPMsgsSys (_ :: map (makePMsgInternal pimpl) _) pimpl);
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

    Ltac syn_trs_init trsIdx topo chgs rqFrom rqTo :=
      assert (SynVChanges
                trsIdx topo chgs
                ((rqFrom, rqTo) :: nil) nil nil) by constructor;
      subst chgs.

    Ltac syn_trs_step :=
      let cur := fresh "cur" in
      let inds := fresh "inds" in
      let msgs := fresh "msgs" in
      evar (cur: list (IdxT * IdxT));
      evar (inds: list IdxT);
      evar (msgs: list PMsg);
      match goal with
      | [H: SynVChanges ?trsIdx ?topo ?chgs ?pcur ?pinds ?pmsgs |- _] =>
        assert (SynVChanges trsIdx topo chgs cur inds msgs)
          by (subst cur inds msgs;
              first [eapply SynVChangeFwd;
                     try eassumption; try reflexivity; try discriminate; fail
                    |eapply SynVChangeImm;
                     try eassumption; try reflexivity; try discriminate; fail]);
        clear H
      end;
      simpl in cur, inds, msgs;
      subst cur inds msgs.

    Ltac syn_trs_rep := repeat syn_trs_step.

    Fixpoint removeEntry efrom hdl pmsgs :=
      match pmsgs with
      | nil => nil
      | pmsg :: pmsgs' =>
        if (if mid_from (pmsg_mid pmsg) ==n efrom then true else false)
             && (if mid_to (pmsg_mid pmsg) ==n hdl then true else false)
        then pmsgs'
        else pmsg :: (removeEntry efrom hdl pmsgs')
      end.

    Ltac syn_trs_ins efrom hdl :=
      match goal with
      | [H: SynVChanges _ _ _ _ _ ?pmsgs |- _] =>
        instantiate (1:= removeEntry efrom hdl pmsgs); clear H
      end.

    Ltac sim_spec_silent :=
      left; do 2 eexists; repeat split;
      [apply SdSlt|reflexivity|].

    Definition svmTrsIdx0 := 0.
    Definition svmTargetOIdx0 := child1Idx.
    Definition svmTargetPMsgIdx0 := 0.

    Definition svmSynTrs0:
      { impl1: System & SynthOk spec (SimTrs SvmR) svmP impl1 }.
    Proof.
      get_target_trs impl0 svmTargetOIdx0 svmTargetPMsgIdx0 ttrs.
      get_pmsg_from ttrs tfrom.
      get_pmsg_precond ttrs tprec.
      find_new_prec tprec svmImplChild1Inv nprec.

      syn_step_init impl0 impl0_ok.

      - (** serializability *) admit.
      - (** simulation *)
        syn_step_sim impl0_ok.
        inv_step_seq.

        + (** silent *)
          simulates_silent.
        + (** external message-in *)
          simulates_lbl_in svmMsgF_ValidMsgMap.

        + (** internal transaction started *)

          (* 1) Prove [In fpmsg (?a :: ?l)]; this is easy. *)
          pose proof (pmsgsOf_in _ _ H1 _ H9).
          apply addPMsgsSys_buildRawSys_sublist in H0.
          
          (* 2) Synthesize [?a] as the only [PMsg] 
           *    accepting the target external request. *)
          instantiate (2:= synRq svmTrsIdx0 svmTargetOIdx0 alwaysLock tfrom _ nprec).

          (* 3-1) Since [fpmsg] here is for the external request,
           *      we get fpmsg = ?a. *)
          inv H0;
            [|apply makePMsgInternal_in_internal in H2; [|discriminate];
              rewrite <-H8 in H2;
              rewrite addPMsgsSys_isExternal, buildRawSys_isExternal in H4;
              exfalso; eapply internal_external_false; eauto].

          (* 3-2) Now we can extract some information 
           *      about the external request.
           *)
          clear H1 H9. (* Do we still need these? *)
          destruct fmsg as [[fmid fval] ftid].
          simpl in H8; subst.
          destruct H6 as [? [? ?]]; simpl in *; subst.

          (* 4) Due to [pmsg_precond fpmsg os], now we can take
           *    the specific precondition for [os]. *)
          destruct H10; hnf in H0.

          (* 5) By using [H: SimTrs ...] and the precondition of [os],
           *    we can guess the entire state invariant. *)
          pose proof H as Hsim.
          inv H; simpl in H5.
          pose proof (simEquiv_OState_eq_1 _ _ H5 _ _ H3 H2).
          destruct H as [ost2 [? ?]].
          rewrite <-H1 in H; unfold svmTargetOIdx0 in *.
          destruct ost2 as [ost2 trsh2], os as [ost trsh]; simpl in *; subst.
          inv H6; try (mv_rewriter; fail).

          (* 6) Prove the existence of a poststate for the target
           *    transaction, in order to build some postcondition.
           *)
          assert (exists poss post,
                     (tst_oss poss)@[child1Idx] = Some post /\
                     (fun st =>
                        (ost_st st) @[ statusIdx] = Some (VNat stS)) post /\
                     SvmR (tst_oss poss) (tst_oss sst1)).
          { admit. }
          destruct H6 as [poss [post ?]]; dest.
          inv H18; try (mv_rewriter; fail).

          (* 7) Now we have enough information about prestate and
           *    poststate! Let's use an Ltac to generate a "diff"
           *    between two states, in order to synthesize [?fwds]
           *    and [?l].
           *)
          destruct poss as [poss pmsgs ptid]; simpl in *.
          mv_rewriter.
          collect_vloc.
          collect_diff rioss poss.
          clear_vloc.
          pose {| vchg_consts := (existT _ _ df) :: (existT _ _ df0) :: nil;
                  vchg_moved := Some (existT _ _ df1) |} as vchgs.
          subst df df0 df1.
          pose (getChangeTargets vchgs) as tgts; cbn in tgts.
          clear tgts.
          instantiate (1:= child1Idx :: child2Idx :: nil).

          (* 8) Let's synthesize [?l] !! *)
          syn_trs_init svmTrsIdx0 (sys_chns impl0) vchgs tfrom child1Idx.
          syn_trs_rep.
          syn_trs_ins tfrom child1Idx.

          (* 9) All [PMsg]s are synthesized! Ready to prove the simulation. *)
          simpl.
          sim_spec_silent.
          unfold synRqPostcond in H11; subst.
          eapply simTrs_preserved_lock_added; eauto.

        + (** internal forwarding *)
          Common.dest_in.
          * (* a request case *)
            simpl in *.
            unfold makeMsgIdInternal in H8; cbn in H8.
            destruct fmsg as [[fmid fval] ftid]; simpl in *.
            subst; simpl in *.
            cbn in H4.
            destruct H6 as [? [? ?]]; simpl in *; subst.
            simpl.
            sim_spec_silent.
            unfold synRqPostcond in H11; subst.
            eapply simTrs_preserved_lock_added; eauto.
          * (* a response case *)
            simpl in *.
            unfold makeMsgIdInternal in H8; cbn in H8.
            destruct fmsg as [[fmid fval] ftid]; simpl in *.
            subst; simpl in *.
            cbn in H4.
            destruct H6 as [? [? ?]]; simpl in *; subst.

            remember (map tmsg_msg _) as outs.
            destruct outs.
            { left.
              do 2 eexists.
              repeat split; [apply SdSlt|reflexivity|].
              admit.
            }
            { exfalso.
              admit.
            }

          * (* the initiating [PMsg] does not belong to
             * internal forwarding cases. *)
            simpl in *.
            destruct fmsg as [[fmid fval] ftid]; simpl in *.
            subst; simpl in *.
            cbn in H4.
            discriminate.

          * (* a response case *)
            admit.

          * (* an immediate response case *)
            admit.

    Admitted.
    
  End SynStep.

End Impl.

