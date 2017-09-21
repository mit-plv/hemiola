Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics SemDet Simulation.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Inductive SVM : Set :=
| GetReq
| GetResp (v: nat)
| SetReq (v: nat)
| SetResp
| InvReq
| InvResp (v: nat).

Definition svm_dec: forall m1 m2: SVM, {m1 = m2} + {m1 <> m2}.
Proof.
  repeat decide equality.
Defined.

Section System.
  Variables extIdx1 extIdx2: nat.

  Section Spec.

    Definition specIdx := 0.
    Definition specChn1 := 1.
    Definition specChn2 := 2.
    Definition valueIdx := 0.

    Definition getSpecExtIdx (idx: nat) :=
      if eq_nat_dec idx specChn1 then extIdx1 else extIdx2.
    
    Section PerChn.
      Variable chnIdx: nat.

      Definition getReqM := buildMsgId (getSpecExtIdx chnIdx) specIdx "SvmGet" Rq chnIdx.
      Definition getRespM := buildMsgId (getSpecExtIdx chnIdx) specIdx "SvmGet" Rs chnIdx.
      Definition setReqM := buildMsgId (getSpecExtIdx chnIdx) specIdx "SvmSet" Rq chnIdx.
      Definition setRespM := buildMsgId (getSpecExtIdx chnIdx) specIdx "SvmSet" Rs chnIdx.

      Definition specGetReq: PMsg :=
        {| pmsg_mid := getReqM;
           pmsg_precond := T;
           pmsg_outs :=
             fun st _ =>
               st@[valueIdx] >>=[nil]
                 (fun v => {| msg_id := getRespM; msg_value := v |} :: nil);
           pmsg_postcond :=
             fun pre _ post => pre = post
        |}.

      Definition specSetReq: PMsg :=
        {| pmsg_mid := setReqM;
           pmsg_precond := T;
           pmsg_outs :=
             fun st _ => {| msg_id := setRespM; msg_value := VUnit |} :: nil;
           pmsg_postcond :=
             fun pre v post => exists n, v = VNat n /\ post@[valueIdx] = Some (VNat n)
        |}.

    End PerChn.

    Definition specObj: Object :=
      {| obj_idx := specIdx;
         obj_state_init := [valueIdx <- VNat 0];
         obj_trs :=
           (specGetReq specChn1)
             :: (specSetReq specChn1)
             :: (specGetReq specChn2)
             :: (specSetReq specChn2) :: nil
      |}.
    
    Definition spec : System := singleton specObj.

  End Spec.

  Section Impl0.

    Definition parentIdx := 0.
    Definition child1Idx := 1.
    Definition child2Idx := 2.
    Definition chnImpl := 0.
    Definition chnC2PRq := 1.
    Definition chnC2PRs := 2.
    
    Definition theOtherChild (idx: nat) :=
      if eq_nat_dec idx child1Idx then child2Idx else child1Idx.
    Definition getImplExtIdx (idx: nat) :=
      if eq_nat_dec idx child1Idx then extIdx1 else extIdx2.

    (* Definition valueIdx := 0. *)
    Definition statusIdx := 1.
    
    Definition stM := 2.
    Definition stS := 1.
    Definition stI := 0.

    Section Child0.
      Variable childIdx: nat.

      Definition ecGetReqM := buildMsgId (getImplExtIdx childIdx) childIdx "SvmGet" Rq chnImpl.
      Definition ecGetRespM := buildMsgId (getImplExtIdx childIdx) childIdx "SvmGet" Rs chnImpl.
      Definition ecSetReqM := buildMsgId (getImplExtIdx childIdx) childIdx "SvmSet" Rq chnImpl.
      Definition ecSetRespM := buildMsgId (getImplExtIdx childIdx) childIdx "SvmSet" Rs chnImpl.

      Definition ecGetReqOk: PMsg :=
        {| pmsg_mid := ecGetReqM;
           pmsg_precond :=
             fun st => st@[statusIdx] >>=[False] 
                         (fun stt => match stt with
                                     | VNat n => n >= stS
                                     | _ => False
                                     end);
           pmsg_outs :=
             fun st _ =>
               st@[valueIdx] >>=[nil]
                 (fun v => {| msg_id := ecGetRespM; msg_value := v |} :: nil);
           pmsg_postcond :=
             fun pre _ post => pre = post
        |}.

      Definition ecSetReqOk: PMsg :=
        {| pmsg_mid := ecSetReqM;
           pmsg_precond :=
             fun st => st@[statusIdx] >>=[False] 
                         (fun stt => match stt with
                                     | VNat n => n = stM
                                     | _ => False
                                     end);
           pmsg_outs :=
             fun st _ => {| msg_id := ecSetRespM; msg_value := VUnit |} :: nil;
           pmsg_postcond :=
             fun pre v post =>
               exists n, v = VNat n /\
                         post = pre +[ valueIdx <- VNat n] |}.

      Definition child0: Object :=
        {| obj_idx := childIdx;
           obj_state_init := [valueIdx <- VNat 0] +[statusIdx <- VNat stS];
           obj_trs := ecGetReqOk :: ecSetReqOk :: nil
        |}.

    End Child0.

    Section Parent0.

      Definition parent0 : Object :=
        {| obj_idx := parentIdx;
           obj_state_init := [valueIdx <- VNat 0] +[statusIdx <- VNat stS];
           obj_trs := nil
        |}.

    End Parent0.

    Definition impl0 : System :=
      {| sys_objs := parent0 :: (child0 child1Idx) :: (child0 child2Idx) :: nil;
         sys_chns :=
           (buildChannel extIdx1 child1Idx chnImpl)
             :: (buildChannel extIdx2 child2Idx chnImpl)
             :: (buildChannel child1Idx parentIdx chnC2PRq)
             :: (buildChannel child1Idx parentIdx chnC2PRs)
             :: (buildChannel child2Idx parentIdx chnC2PRq)
             :: (buildChannel child2Idx parentIdx chnC2PRs)
             :: (buildChannel parentIdx child1Idx chnImpl)
             :: (buildChannel parentIdx child2Idx chnImpl)
             :: nil
      |}.

  End Impl0.

End System.


Section Sim.
  Variables extIdx1 extIdx2: nat.
  Hypotheses (Hiext1: isExternal (impl0 extIdx1 extIdx2) extIdx1 = true)
             (Hiext2: isExternal (impl0 extIdx1 extIdx2) extIdx2 = true)
             (Hsext1: isExternal (spec extIdx1 extIdx2) extIdx1 = true)
             (Hsext2: isExternal (spec extIdx1 extIdx2) extIdx2 = true).

  Local Notation impl0 := (impl0 extIdx1 extIdx2).
  Local Notation spec := (spec extIdx1 extIdx2).

  Definition svmIdxF (idx: IdxT): IdxT :=
    if idx ?<n (indicesOf impl0) then specIdx else idx.

  Definition svmMsgIdF (imid: MsgId): MsgId :=
    {| mid_rq := svmIdxF (mid_rq imid);
       mid_rs := svmIdxF (mid_rs imid);
       mid_type := mid_type imid;
       mid_rqrs := mid_rqrs imid;
       mid_chn := mid_rs imid |}.

  Definition svmMsgF (imsg: Msg): Msg :=
    {| msg_id := svmMsgIdF (msg_id imsg);
       msg_value := msg_value imsg |}.

  Definition svmMsgsF (imsgs: list Msg): list Msg :=
    map svmMsgF imsgs.

  Definition svmP (b: BLabel) :=
    {| blbl_ins := svmMsgsF (blbl_ins b);
       blbl_outs := svmMsgsF (blbl_outs b) |}.

  Definition SvmWf (os: StateT) v stt :=
    os@[valueIdx] = Some v /\ os@[statusIdx] = Some stt.

  Inductive ValidValue: ObjectStates -> Value -> Prop :=
  | VVM1: forall s ost vv,
      s@[child1Idx] = Some ost ->
      ost@[statusIdx] = Some (VNat stM) ->
      ost@[valueIdx] = Some vv ->
      ValidValue s vv
  | VVM2: forall s ost vv,
      s@[child2Idx] = Some ost ->
      ost@[statusIdx] = Some (VNat stM) ->
      ost@[valueIdx] = Some vv ->
      ValidValue s vv
  | VVS: forall s ost1 ost2 vv,
      s@[child1Idx] = Some ost1 ->
      s@[child2Idx] = Some ost2 ->
      ost1@[statusIdx] = Some (VNat stS) ->
      ost2@[statusIdx] = Some (VNat stS) ->
      ost1@[valueIdx] = Some vv ->
      ost2@[valueIdx] = Some vv ->
      ValidValue s vv.

  Inductive SvmStR: ObjectStates -> ObjectStates -> Prop :=
  | SvmStRIntro:
      forall ist sst sost v iost1 iost2 iostp v1 stt1 v2 stt2 vp sttp,
        sst@[specIdx] = Some sost ->
        sost@[valueIdx] = Some v ->
        ist@[child1Idx] = Some iost1 ->
        ist@[child2Idx] = Some iost2 ->
        ist@[parentIdx] = Some iostp ->
        SvmWf iost1 v1 stt1 ->
        SvmWf iost2 v2 stt2 ->
        SvmWf iostp vp sttp ->
        ValidValue ist v ->
        SvmStR ist sst.

  Definition SvmMsgsR (imsgs smsgs: Messages) :=
    forall to,
      imsgs@[to] >>=[True]
      (fun imf =>
         forall from,
           imf@[from] >>=[True]
           (fun ichn =>
              forall cidx,
                ichn@[cidx] >>=[True]
                (fun iq =>
                   smsgs@[svmIdxF to] >>=[False]
                   (fun smf =>
                      smf@[svmIdxF from] >>=[False]
                      (fun schn =>
                         schn@[to] >>=[False] (fun sq => sq = svmMsgsF iq)))))).

  Definition SvmR (ist sst: State) :=
    SvmStR (st_oss ist) (st_oss sst) /\ SvmMsgsR (st_msgs ist) (st_msgs sst).

  Theorem svm_simulation_init:
     SvmR (getStateInit impl0) (getStateInit spec).
  Proof.
    econstructor; try (split; reflexivity).
    econstructor; try reflexivity; try (split; reflexivity).
    eapply VVS; reflexivity.
  Qed.
  Hint Resolve svm_simulation_init.

  Ltac rewriter :=
    repeat
      match goal with
      | [H: True |- _] => clear H
      | [H: False |- _] => elim H
      | [H: Some _ = Some _ |- _] => inv H
      | [H: Some _ = None |- _] => discriminate
      | [H: None = Some _ |- _] => discriminate

      | [H: M.find ?k ?m = Some _ |- context[M.find ?k ?m] ] => rewrite H; simpl
      | [H: M.find ?k ?m = None |- context[M.find ?k ?m] ] => rewrite H; simpl
      | [H: Some _ = M.find ?k ?m |- context[M.find ?k ?m] ] => rewrite <-H; simpl
      | [H: None = M.find ?k ?m |- context[M.find ?k ?m] ] => rewrite <-H; simpl
      | [H1: M.find ?k ?m = Some _, H2: context[M.find ?k ?m] |- _] =>
        rewrite H1 in H2; simpl in H2
      | [H1: M.find ?k ?m = None, H2: context[M.find ?k ?m] |- _] =>
        rewrite H1 in H2; simpl in H2
      | [H1: Some _ = M.find ?k ?m, H2: context[M.find ?k ?m] |- _] =>
        rewrite <-H1 in H2; simpl in H2
      | [H1: None = M.find ?k ?m, H2: context[M.find ?k ?m] |- _] =>
        rewrite <-H1 in H2; simpl in H2

      | [H: ?te >>=[False] _ |- _] =>
        let t := fresh "t" in
        remember te as t; destruct t; simpl in H
      end.

  Lemma svmIdxF_extIdx1: svmIdxF extIdx1 = extIdx1.
  Proof.
    unfold isExternal, svmIdxF in *; destruct (extIdx1 ?<n _); [discriminate|auto].
  Qed.

  Lemma svmIdxF_extIdx2: svmIdxF extIdx2 = extIdx2.
  Proof.
    unfold isExternal, svmIdxF in *; destruct (extIdx2 ?<n _); [discriminate|auto].
  Qed.

  Theorem svm_simulation: Simulates step_mod SvmR svmP impl0 spec.
  Proof.
    unfold Simulates; intros.

    apply step_mod_step_det in H0; inv H0.

    - (* silent *)
      unfold emptyLabel; rewrite toBLabel_None.
      simpl; eauto.

    - (* internal *)
      destruct H; inv H; unfold st_oss, st_msgs in *.
      destruct sst1 as [ost1 msgs1].
      Common.dest_in.
      + destruct fmsg as [[frq frs fty frr fch] fval]; simpl in *.
        inv H6; inv H7; simpl in *.
        cbn in H1, H5; dest; subst.
        specialize (H0 child1Idx); rewriter.
        specialize (H0 extIdx1); apply firstMF_Some_inv in H5; dest; rewriter.
        specialize (H0 chnImpl); apply firstC_Some_inv in H5; dest; rewriter.
        subst.
        destruct x0 as [|ffq fq]; [discriminate|]; simpl in H5; inv H5.
        inv H6.
        
        rewrite toBLabel_Some_2 by (inv H15; rewriter; cbn; rewrite Hiext1; discriminate).
        do 2 eexists; split.
        * apply step_det_step_mod.
          eapply SdInt; try reflexivity.
          { left; reflexivity. }
          { eassumption. }
          { simpl; cbn in Heqt0; rewriter; reflexivity. }
          { instantiate (3:= extIdx1).
            instantiate (2:= child1Idx).
            unfold firstMF.
            rewrite svmIdxF_extIdx1 in Heqt1; rewrite <-Heqt1; simpl.
            unfold firstC; rewrite <-Heqt2; simpl.
            reflexivity.
          }
          { instantiate (1:= specGetReq extIdx1 extIdx2 specChn1).
            unfold svmMsgF, svmMsgIdF; cbn.
            rewrite svmIdxF_extIdx1.
            reflexivity.
          }
          { unfold svmMsgF, svmMsgIdF; cbn.
            repeat split; cbn.
            apply svmIdxF_extIdx1.
          }
          { left; reflexivity. }
          { simpl; auto. }
          { simpl; reflexivity. }
        * rewrite toBLabel_Some_2 by (cbn; rewriter; cbn; rewrite Hsext1; discriminate).
          admit.
          
      + admit.
      + admit.
      + admit.
        
    - (* external *)
      rewrite toBLabel_Some_1 by assumption.
      exists {| st_oss := st_oss sst1;
                st_msgs := distributeMsgs (svmMsgsF emsgs) (st_msgs sst1) |}.
      exists {| lbl_ins := svmMsgsF emsgs; lbl_hdl := None; lbl_outs := nil |}.
      split; [|split].
      + apply step_det_step_mod.
        destruct sst1 as [oss1 oims1]; simpl.
        eapply SdExt with (from:= from); eauto.
        * intro Hx; elim H1; clear H1.
          Common.dest_in; simpl; tauto.
        * destruct emsgs; auto.
          discriminate.
        * clear -H3; induction emsgs; simpl; [apply SubList_nil|].
          apply SubList_cons_inv in H3; dest.
          apply SubList_cons; auto.
          clear -H.
          Common.dest_in;
            destruct a as [[mrq mrs mty [|] mch] ?];
            unfold svmMsgIdF, msgTo in *; simpl in *; subst; auto.
      + rewrite toBLabel_Some_1 by (destruct emsgs; [auto|discriminate]).
        reflexivity.
      + inv H.
        econstructor; eauto.
  Admitted.
  Hint Resolve svm_simulation.

  Theorem impl0_refines_spec: step_mod |-- impl0 ⊑[svmP] spec.
  Proof.
    apply simulation_implies_refinement with (sim:= SvmR); auto.
  Qed.

End Sim.

