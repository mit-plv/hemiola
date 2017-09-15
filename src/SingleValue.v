Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics Simulation.

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
    Definition specChn1 := 0.
    Definition specChn2 := 1.
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

  Inductive ValidValue: State -> Value -> Prop :=
  | VVM1: forall s ost vv,
      (st_oss s)@[child1Idx] = Some ost ->
      ost@[statusIdx] = Some (VNat stM) ->
      ost@[valueIdx] = Some vv ->
      ValidValue s vv
  | VVM2: forall s ost vv,
      (st_oss s)@[child2Idx] = Some ost ->
      ost@[statusIdx] = Some (VNat stM) ->
      ost@[valueIdx] = Some vv ->
      ValidValue s vv
  | VVS: forall s ost1 ost2 vv,
      (st_oss s)@[child1Idx] = Some ost1 ->
      (st_oss s)@[child2Idx] = Some ost2 ->
      ost1@[statusIdx] = Some (VNat stS) ->
      ost2@[statusIdx] = Some (VNat stS) ->
      ost1@[valueIdx] = Some vv ->
      ost2@[valueIdx] = Some vv ->
      ValidValue s vv.

  Inductive SvmR: State -> State -> Prop :=
  | SvmRIntro: forall ist sst st v,
      (st_oss sst)@[specIdx] = Some st ->
      st@[valueIdx] = Some v ->
      ValidValue ist v ->
      SvmR ist sst.

  Theorem svm_simulation_init:
     SvmR (getStateInit (impl0 extIdx1 extIdx2))
          (getStateInit (spec extIdx1 extIdx2)).
  Proof.
    econstructor; try reflexivity.
    eapply VVS; reflexivity.
  Qed.
  Hint Resolve svm_simulation_init.

  Definition svmMsgIdF (imid: MsgId): MsgId :=
    {| mid_rq := mid_rq imid;
       mid_rs := specIdx;
       mid_type := mid_type imid;
       mid_rqrs := mid_rqrs imid;
       mid_chn := mid_rs imid |}.

  Definition svmMsgF (imsg: Msg): Msg :=
    {| msg_id := svmMsgIdF (msg_id imsg);
       msg_value := msg_value imsg |}.

  Lemma svmMsgF_value:
    forall m, msg_value (svmMsgF m) = msg_value m.
  Proof. reflexivity. Qed.

  Definition svmMsgsF (imsgs: list Msg): list Msg :=
    map svmMsgF imsgs.

  Lemma svmMsgsF_value:
    forall msgs, map msg_value (svmMsgsF msgs) = map msg_value msgs.
  Proof.
    induction msgs; simpl; intros; auto.
    rewrite IHmsgs; reflexivity.
  Qed.

  Lemma svmMsgsF_validOuts:
    forall from msgs, ValidOuts from msgs ->
                      ValidOuts from (svmMsgsF msgs).
  Proof.
  Admitted.

  Theorem svm_simulation: Simulates SvmR (impl0 extIdx1 extIdx2) (spec extIdx1 extIdx2).
  Proof.
    unfold Simulates; intros.

    apply step_step_det in H0; inv H0.

    - (* silent *) simpl; eauto.

    - (* internal *)
      admit.

    - (* external *)
      rewrite toELabel_Some_1 by assumption.
      exists {| st_oss := st_oss sst1;
                st_msgs := distributeMsgs (svmMsgsF emsgs) (st_msgs sst1) |}.
      exists {| lbl_ins := svmMsgsF emsgs; lbl_hdl := None; lbl_outs := nil |}.
      split; [|split].
      + apply step_det_step.
        destruct sst1 as [oss1 oims1]; simpl.
        eapply SsdExt with (from:= from); eauto.
        * intro Hx; elim H1; clear H1.
          Common.dest_in; simpl; tauto.
        * destruct emsgs; auto.
          discriminate.
        * apply svmMsgsF_validOuts; auto.
        * clear; induction emsgs; simpl; [apply SubList_nil|].
          admit.
      + rewrite toELabel_Some_1 by (destruct emsgs; [auto|discriminate]).
        rewrite svmMsgsF_value; reflexivity.
      + inv H.
        econstructor; eauto.
        inv H6; [eapply VVM1; eauto|eapply VVM2; eauto|eapply VVS; eauto].
  Admitted.
  Hint Resolve svm_simulation.

  Theorem impl0_refines_spec: (impl0 extIdx1 extIdx2) ⊑ (spec extIdx1 extIdx2).
  Proof.
    apply simulation_implies_refinement with (sim:= SvmR); auto.
  Qed.

End Sim.

