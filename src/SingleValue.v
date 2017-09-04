Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics Synthesis.

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
    Definition specChn := 0. (* A single channel is enough. *)
    Definition valueIdx := 0.

    Section PerExt.
      Variable extIdx: nat.

      Definition getReqM := buildMsgId extIdx specIdx "SvmGet" Rq specChn.
      Definition getRespM := buildMsgId extIdx specIdx "SvmGet" Rs specChn.
      Definition setReqM := buildMsgId extIdx specIdx "SvmSet" Rq specChn.
      Definition setRespM := buildMsgId extIdx specIdx "SvmSet" Rs specChn.

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

    End PerExt.

    Definition specObj: Object :=
      {| obj_idx := specIdx;
         obj_state_init := [valueIdx <- VNat 0];
         obj_trs :=
           (specGetReq extIdx1)
             :: (specSetReq extIdx1)
             :: (specGetReq extIdx2)
             :: (specSetReq extIdx2) :: nil
      |}.
    
    Definition spec : System := singleton specObj.

  End Spec.

  Section ImplInit.

    Definition parentIdx := 0.
    Definition child1Idx := 1.
    Definition child2Idx := 2.
    Definition chnImpl := 0.
    Definition chnC2PRq := 1.
    Definition chnC2PRs := 2.
    
    Definition theOtherChild (idx: nat) :=
      if eq_nat_dec idx child1Idx then child2Idx else child1Idx.
    Definition getExtIdx (idx: nat) :=
      if eq_nat_dec idx child1Idx then extIdx1 else extIdx2.

    (* Definition valueIdx := 0. *)
    Definition statusIdx := 1.
    
    Definition stM := 2.
    Definition stS := 1.
    Definition stI := 0.

    Section ChildInit.
      Variable childIdx: nat.

      Definition ecGetReqM := buildMsgId (getExtIdx childIdx) childIdx "SvmGet" Rq chnImpl.
      Definition ecGetRespM := buildMsgId (getExtIdx childIdx) childIdx "SvmGet" Rs chnImpl.
      Definition ecSetReqM := buildMsgId (getExtIdx childIdx) childIdx "SvmSet" Rq chnImpl.
      Definition ecSetRespM := buildMsgId (getExtIdx childIdx) childIdx "SvmSet" Rs chnImpl.

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

      Definition child: Object :=
        {| obj_idx := childIdx;
           obj_state_init := [valueIdx <- VNat 0] +[statusIdx <- VNat stS];
           obj_trs := ecGetReqOk :: ecSetReqOk :: nil
        |}.

    End ChildInit.

    Section ParentInit.

      Definition parent : Object :=
        {| obj_idx := parentIdx;
           obj_state_init := [valueIdx <- VNat 0] +[statusIdx <- VNat stS];
           obj_trs := nil
        |}.

    End ParentInit.

    Definition implInit : System :=
      {| sys_objs := parent :: (child child1Idx) :: (child child2Idx) :: nil;
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

  End ImplInit.

End System.


