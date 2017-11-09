Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics.
Require Import StepDet StepSeq.

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

  Definition SvmGetE: IdxT := 0.
  Definition SvmSetE: IdxT := 1.

  Section Spec.

    Definition specIdx := 0.
    Definition specChn1 := 1.
    Definition specChn2 := 2.
    Definition valueIdx := 0.

    Definition getSpecExtIdx (idx: nat) :=
      if eq_nat_dec idx specChn1 then extIdx1 else extIdx2.
    
    Section PerChn.
      Variable chnIdx: nat.

      Definition getReqM := buildMsgId SvmGetE (getSpecExtIdx chnIdx) specIdx chnIdx.
      Definition getRespM := buildMsgId SvmGetE specIdx (getSpecExtIdx chnIdx) chnIdx.
      Definition setReqM := buildMsgId SvmSetE (getSpecExtIdx chnIdx) specIdx chnIdx.
      Definition setRespM := buildMsgId SvmSetE specIdx (getSpecExtIdx chnIdx) chnIdx.

      Definition specGetReq: PMsg :=
        {| pmsg_mid := getReqM;
           pmsg_precond := T;
           pmsg_outs :=
             fun st _ =>
               (ost_st st)@[valueIdx] >>=[nil]
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
             fun pre v post => (ost_st post)@[valueIdx] = Some v
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

      Definition ecGetReqM := buildMsgId SvmGetE (getImplExtIdx childIdx) childIdx chnImpl.
      Definition ecGetRespM := buildMsgId SvmGetE childIdx (getImplExtIdx childIdx) chnImpl.
      Definition ecSetReqM := buildMsgId SvmSetE (getImplExtIdx childIdx) childIdx chnImpl.
      Definition ecSetRespM := buildMsgId SvmSetE childIdx (getImplExtIdx childIdx) chnImpl.

      Definition ecGetReqOk: PMsg :=
        {| pmsg_mid := ecGetReqM;
           pmsg_precond :=
             fun st => (ost_st st)@[statusIdx] = Some (VNat stS) \/
                       (ost_st st)@[statusIdx] = Some (VNat stM);
           pmsg_outs :=
             fun st _ =>
               (ost_st st)@[valueIdx] >>=[nil]
                          (fun v => {| msg_id := ecGetRespM; msg_value := v |} :: nil);
           pmsg_postcond :=
             fun pre _ post => pre = post
        |}.

      Definition ecSetReqOk: PMsg :=
        {| pmsg_mid := ecSetReqM;
           pmsg_precond :=
             fun st => (ost_st st)@[statusIdx] = Some (VNat stM);
           pmsg_outs :=
             fun st _ => {| msg_id := ecSetRespM; msg_value := VUnit |} :: nil;
           pmsg_postcond :=
             fun pre v post =>
               exists n, v = VNat n /\
                         ost_st post = (ost_st pre) +[ valueIdx <- VNat n] |}.

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

