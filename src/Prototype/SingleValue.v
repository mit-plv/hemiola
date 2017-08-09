Require Import List String Peano_dec.
Require Import FMap Language.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Inductive SVMType :=
| SvmGet
| SvmSet
| SvmInv.

Definition svmT_dec: forall m1 m2: SVMType, {m1 = m2} + {m1 <> m2}.
Proof.
  decide equality.
Defined.

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

Notation "'T'" := (fun _ => True).
Notation "'TT'" := (fun pre _ post => pre = post).

Definition msgsInit {MsgT ValT}: M.t (list (Msg MsgT ValT)) :=
  [] +[rrToNat Rq <- nil]+[rrToNat Rs <- nil].

Section System.
  Variables extIdx1 extIdx2: nat.

  Section Spec.

    Definition specIdx := 0.
    Definition specChn := 0. (* A single channel is enough. *)
    Definition SpecState := nat. (* a single value *)

    Section PerExt.
      Variable extIdx: nat.

      Definition getReqM := buildMsgId extIdx specIdx SvmGet Rq specChn.
      Definition getRespM := buildMsgId extIdx specIdx SvmGet Rs specChn.
      Definition setReqM := buildMsgId extIdx specIdx SvmSet Rq specChn.
      Definition setRespM := buildMsgId extIdx specIdx SvmSet Rs specChn.

      Definition specGetReq: PMsg SVMType SVM SpecState :=
        {| pmsg_mid := getReqM;
           pmsg_precond := T;
           pmsg_outs :=
             fun st _ => {| msg_id := getRespM; msg_value := GetResp st |} :: nil;
           pmsg_postcond :=
             fun pre msg post => pre = post
        |}.

      Definition specSetReq: PMsg SVMType SVM SpecState :=
        {| pmsg_mid := setReqM;
           pmsg_precond := T;
           pmsg_outs :=
             fun st _ => {| msg_id := setRespM; msg_value := SetResp |} :: nil;
           pmsg_postcond :=
             fun pre msg post =>
               exists v : nat, msg = SetReq v /\ post = v
        |}.

    End PerExt.

    Definition specObj: Object SVMType SVM SpecState :=
      {| obj_idx := specIdx;
         obj_state_init := 0;
         obj_pmsgs :=
           (specGetReq extIdx1)
             :: (specSetReq extIdx1)
             :: (specGetReq extIdx2)
             :: (specSetReq extIdx2) :: nil
      |}.
    
    Definition spec : System SVMType SVM SpecState := specObj :: nil.

  End Spec.

  Section Impl.

    Definition parentIdx := 0.
    Definition child1Idx := 1.
    Definition child2Idx := 2.
    Definition implChn := 0. (* A single channel is enough..? *)
    Definition theOtherChild (idx: nat) :=
      if eq_nat_dec idx child1Idx then child2Idx else child1Idx.
    Definition getExtIdx (idx: nat) :=
      if eq_nat_dec idx child1Idx then extIdx1 else extIdx2.

    Inductive ValStatus := Valid | Invalid.
    Inductive TrsStatus := NoTrs | Trs (isGet: bool).

    Record ImplState :=
      { impl_status : ValStatus;
        impl_trs : TrsStatus;
        impl_value_trs : nat;
        impl_value : nat
      }.

    Section Child.
      Variable childIdx: nat.

      Definition ecGetReqM := buildMsgId (getExtIdx childIdx) childIdx SvmGet Rq implChn.
      Definition ecGetRespM := buildMsgId (getExtIdx childIdx) childIdx SvmGet Rs implChn.
      Definition ecSetReqM := buildMsgId (getExtIdx childIdx) childIdx SvmSet Rq implChn.
      Definition ecSetRespM := buildMsgId (getExtIdx childIdx) childIdx SvmSet Rs implChn.
      Definition cpGetReqM := buildMsgId childIdx parentIdx SvmGet Rq implChn.
      Definition cpGetRespM := buildMsgId childIdx parentIdx SvmGet Rs implChn.
      Definition cpSetReqM := buildMsgId childIdx parentIdx SvmSet Rq implChn.
      Definition cpSetRespM := buildMsgId childIdx parentIdx SvmSet Rs implChn.
      Definition pcInvReqM := buildMsgId parentIdx childIdx SvmInv Rq implChn.
      Definition pcInvRespM := buildMsgId parentIdx childIdx SvmInv Rs implChn.

      Definition ecGetReqValid: PMsg SVMType SVM ImplState :=
        {| pmsg_mid := ecGetReqM;
           pmsg_precond := fun st => impl_status st = Valid;
           pmsg_outs :=
             fun st _ => {| msg_id := ecGetRespM;
                            msg_value := GetResp (impl_value st) |} :: nil;
           pmsg_postcond :=
             fun pre msg post =>
               msg = GetReq /\ pre = post
        |}.
      
      Definition ecGetReqInvalid: PMsg SVMType SVM ImplState :=
        {| pmsg_mid := ecGetReqM;
           pmsg_precond := fun st => impl_status st = Invalid;
           pmsg_outs :=
             fun st _ => {| msg_id := cpGetReqM;
                            msg_value := GetReq |} :: nil;
           pmsg_postcond :=
             fun pre msg post =>
               msg = GetReq /\ impl_trs post = Trs true
      |}.

      Definition ecSetReqValid: PMsg SVMType SVM ImplState :=
        {| pmsg_mid := ecSetReqM;
           pmsg_precond := fun st => impl_status st = Valid;
           pmsg_outs :=
             fun st _ => {| msg_id := ecSetRespM;
                            msg_value := SetResp |} :: nil;
           pmsg_postcond :=
             fun pre msg post =>
               exists v, msg = SetReq v /\
                         impl_status post = Valid /\
                         impl_value post = v
        |}.

      Definition ecSetReqInvalid: PMsg SVMType SVM ImplState :=
        {| pmsg_mid := ecSetReqM;
           pmsg_precond := fun st => impl_status st = Invalid;
           pmsg_outs :=
             fun st msg =>
               match msg with
               | SetReq v => {| msg_id := cpSetReqM;
                                msg_value := SetReq v |} :: nil
               | _ => nil
               end;
           pmsg_postcond :=
             fun pre msg post =>
               exists v, msg = SetReq v /\
                         impl_trs post = Trs false /\
                         impl_value_trs post = v
        |}.

      Definition cpGetResp: PMsg SVMType SVM ImplState :=
        {| pmsg_mid := cpGetRespM;
           pmsg_precond := T;
           pmsg_outs :=
             fun st msg =>
               match msg with
               | GetResp v => {| msg_id := ecGetRespM;
                                 msg_value := GetResp v |} :: nil
               | _ => nil
               end;
           pmsg_postcond :=
             fun pre msg post =>
               exists v, msg = GetResp v /\
                         impl_status post = Valid /\
                         impl_value post = v
        |}.

      Definition cpSetResp: PMsg SVMType SVM ImplState :=
        {| pmsg_mid := cpSetRespM;
           pmsg_precond := T;
           pmsg_outs :=
             fun st _ => {| msg_id := ecSetRespM;
                            msg_value := SetResp |} :: nil;
           pmsg_postcond :=
             fun pre msg post =>
               msg = SetResp /\
               impl_status post = Valid /\
               impl_value post = impl_value_trs pre
        |}.

      Definition pcInvReq: PMsg SVMType SVM ImplState :=
        {| pmsg_mid := pcInvReqM;
           pmsg_precond := fun st => impl_status st = Valid;
           pmsg_outs :=
             fun st _ => {| msg_id := pcInvRespM;
                            msg_value := InvResp (impl_value st) |} :: nil;
           pmsg_postcond :=
             fun pre msg post =>
               msg = InvReq /\ impl_status post = Invalid
        |}.

      Definition child: Object SVMType SVM ImplState :=
        {| obj_idx := childIdx;
           obj_state_init := {| impl_status := Invalid;
                                impl_trs := NoTrs;
                                impl_value_trs := 0;
                                impl_value := 0 |};
           obj_pmsgs := cpGetResp
                          :: cpSetResp
                          :: pcInvReq
                          :: ecGetReqValid
                          :: ecGetReqInvalid
                          :: ecSetReqValid
                          :: ecSetReqInvalid :: nil
        |}.

    End Child.

    Section Parent.

      Definition cpGetReqValid childIdx: PMsg SVMType SVM ImplState :=
        {| pmsg_mid := cpGetReqM childIdx;
           pmsg_precond := fun st => impl_status st = Valid;
           pmsg_outs :=
             fun st _ => {| msg_id := cpGetRespM childIdx;
                            msg_value := GetResp (impl_value st) |} :: nil;
           pmsg_postcond :=
             fun pre msg post =>
               msg = GetReq /\ impl_status post = Invalid
        |}.
      
      Definition cpGetReqInvalid childIdx: PMsg SVMType SVM ImplState :=
        {| pmsg_mid := cpGetReqM childIdx;
           pmsg_precond := fun st => impl_status st = Invalid;
           pmsg_outs :=
             fun st _ => {| msg_id := pcInvReqM childIdx;
                            msg_value := InvReq |} :: nil;
           pmsg_postcond :=
             fun pre msg post =>
               msg = GetReq /\ impl_trs post = Trs true
        |}.

      Definition cpSetReqValid childIdx: PMsg SVMType SVM ImplState :=
        {| pmsg_mid := cpSetReqM childIdx;
           pmsg_precond := fun st => impl_status st = Valid;
           pmsg_outs :=
             fun st _ => {| msg_id := cpSetRespM childIdx;
                            msg_value := SetResp |} :: nil;
           pmsg_postcond :=
             fun pre msg post =>
               exists v, msg = SetReq v /\
                         impl_status post = Invalid
        |}.
      
      Definition cpSetReqInvalid childIdx: PMsg SVMType SVM ImplState :=
        {| pmsg_mid := cpSetReqM childIdx;
           pmsg_precond := fun st => impl_status st = Invalid;
           pmsg_outs :=
             fun st _ => {| msg_id := pcInvReqM childIdx;
                            msg_value := InvReq |} :: nil;
           pmsg_postcond :=
             fun pre msg post =>
               exists v, msg = SetReq v /\
                         impl_trs post = Trs false
        |}.

      Definition pcInvRespGet childIdx: PMsg SVMType SVM ImplState :=
        {| pmsg_mid := pcInvRespM childIdx;
           pmsg_precond := fun st => impl_trs st = Trs true;
           pmsg_outs :=
             fun st msg =>
               match msg with
               | InvResp v => {| msg_id := cpGetRespM childIdx;
                                 msg_value := GetResp v |} :: nil
               | _ => nil
               end;
           pmsg_postcond :=
             fun pre msg post =>
               exists v, msg = InvResp v /\
                         impl_status post = Invalid
        |}.
      
      Definition pcInvRespSet childIdx: PMsg SVMType SVM ImplState :=
        {| pmsg_mid := pcInvRespM childIdx;
           pmsg_precond := fun st => impl_trs st = Trs false;
           pmsg_outs :=
             fun st _ => {| msg_id := cpSetRespM childIdx;
                            msg_value := SetResp |} :: nil;
           pmsg_postcond :=
             fun pre msg post =>
               exists v, msg = InvResp v /\
                         impl_status post = Invalid
        |}.

      Definition parent : Object SVMType SVM ImplState :=
        {| obj_idx := parentIdx;
           obj_state_init := {| impl_status := Valid;
                                impl_trs := NoTrs;
                                impl_value_trs := 0;
                                impl_value := 0 |};
           obj_pmsgs :=
             (cpGetReqValid child1Idx)
               :: (cpGetReqInvalid child1Idx)
               :: (cpSetReqValid child1Idx)
               :: (cpSetReqInvalid child1Idx)
               :: (pcInvRespGet child1Idx)
               :: (pcInvRespSet child1Idx)
               :: (cpGetReqValid child2Idx)
               :: (cpGetReqInvalid child2Idx)
               :: (cpSetReqValid child2Idx)
               :: (cpSetReqInvalid child2Idx)
               :: (pcInvRespGet child2Idx)
               :: (pcInvRespSet child2Idx) :: nil
        |}.

    End Parent.

    Definition impl : System SVMType SVM ImplState :=
      parent :: (child child1Idx) :: (child child2Idx) :: nil.

  End Impl.

End System.

