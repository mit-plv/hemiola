Require Import List String Peano_dec.
Require Import FnMap Language.

Set Implicit Arguments.

Open Scope list.

Inductive SingleValueMsg : Set :=
(* external *)
| GetReq : SingleValueMsg
| GetResp (v: nat) : SingleValueMsg
| SetReq (v: nat) : SingleValueMsg
| SetResp : SingleValueMsg
(* internal *)
| InvReq : SingleValueMsg
| InvResp (v: nat) : SingleValueMsg.

Notation "'T'" := (fun _ => True).
Notation "'TT'" := (fun pre _ post => pre = post).

Section System.
  Variables extIdx1 extIdx2: nat.

  Section Spec.

    Definition specIdx := 0.
    Definition SpecState := nat. (* a single value *)

    Section PerExt.
      Variable extIdx: nat.

      Definition getReqM := buildMsgId extIdx specIdx Rq.
      Definition getRespM := buildMsgId extIdx specIdx Rs.
      Definition setReqM := buildMsgId extIdx specIdx Rq.
      Definition setRespM := buildMsgId extIdx specIdx Rs.

      Definition specGetReq: PMsg SingleValueMsg SpecState :=
        Pmsg getReqM T
             (fun st _ => {| msg_id := getRespM; msg_content := GetResp st |} :: nil)
             (fun pre msg post => pre = post).
      Definition specSetReq: PMsg SingleValueMsg SpecState :=
        Pmsg setReqM T
             (fun st _ => {| msg_id := setRespM; msg_content := SetResp |} :: nil)
             (fun pre msg post => exists v, msg = SetReq v /\ post = v).

    End PerExt.

    Definition specObj: Object SingleValueMsg SpecState :=
      {| obj_idx := 0;
         obj_state_init := 0;
         obj_pmsgs :=
           (specGetReq extIdx1)
             :: (specSetReq extIdx1)
             :: (specGetReq extIdx2)
             :: (specSetReq extIdx2) :: nil
      |}.
    
    Definition spec : System SingleValueMsg SpecState := specObj :: nil.

  End Spec.

  Section Impl.

    Definition parentIdx := 0.
    Definition child1Idx := 1.
    Definition child2Idx := 2.
    Definition theOtherChild (idx: nat) :=
      if eq_nat_dec idx child1Idx then child2Idx else child1Idx.
    Definition getExtIdx (idx: nat) :=
      if eq_nat_dec idx child1Idx then extIdx1 else extIdx2.

    Inductive ValStatus :=
    | Invalid
    | Transient (* only for children *)
    | Valid
    | GetWait (* only for parent *)
    | SetWait (* only for parent *).

    Record ImplState :=
      { impl_status : ValStatus;
        impl_value_trs : nat;
        impl_value : nat
      }.

    Section Child.
      Variable childIdx: nat.

      Definition ecGetReqM := buildMsgId (getExtIdx childIdx) childIdx Rq.
      Definition ecGetRespM := buildMsgId (getExtIdx childIdx) childIdx Rs.
      Definition ecSetReqM := buildMsgId (getExtIdx childIdx) childIdx Rq.
      Definition ecSetRespM := buildMsgId (getExtIdx childIdx) childIdx Rs.
      Definition cpGetReqM := buildMsgId childIdx parentIdx Rq.
      Definition cpGetRespM := buildMsgId childIdx parentIdx Rs.
      Definition cpSetReqM := buildMsgId childIdx parentIdx Rq.
      Definition cpSetRespM := buildMsgId childIdx parentIdx Rs.
      Definition pcInvReqM := buildMsgId parentIdx childIdx Rq.
      Definition pcInvRespM := buildMsgId parentIdx childIdx Rs.

      Definition ecGetReqValid: PMsg SingleValueMsg ImplState :=
        Pmsg ecGetReqM
             (fun st => impl_status st = Valid)
             (fun st _ => {| msg_id := ecGetRespM;
                             msg_content := GetResp (impl_value st) |} :: nil)
             (fun pre msg post => msg = GetReq /\ pre = post).
      
      Definition ecGetReqInvalid: PMsg SingleValueMsg ImplState :=
        Pmsg ecGetReqM
             (fun st => impl_status st = Invalid)
             (fun st _ => {| msg_id := cpGetReqM;
                             msg_content := GetReq |} :: nil)
             (fun pre msg post => msg = GetReq /\ impl_status post = Transient).

      Definition ecSetReqValid: PMsg SingleValueMsg ImplState :=
        Pmsg ecSetReqM
             (fun st => impl_status st = Valid)
             (fun st _ => {| msg_id := ecSetRespM;
                             msg_content := SetResp |} :: nil)
             (fun pre msg post => exists v, msg = SetReq v /\
                                            impl_status post = Valid /\
                                            impl_value post = v).

      Definition ecSetReqInvalid: PMsg SingleValueMsg ImplState :=
        Pmsg ecSetReqM
             (fun st => impl_status st = Invalid)
             (fun st msg =>
                match msg with
                | SetReq v => {| msg_id := cpSetReqM;
                                 msg_content := SetReq v |} :: nil
                | _ => nil
                end)
             (fun pre msg post => exists v, msg = SetReq v /\
                                            impl_status post = Transient /\
                                            impl_value_trs post = v).

      Definition cpGetResp: PMsg SingleValueMsg ImplState :=
        Pmsg cpGetRespM T
             (fun st msg =>
                match msg with
                | GetResp v => {| msg_id := ecGetRespM;
                                  msg_content := GetResp v |} :: nil
                | _ => nil
                end)
             (fun pre msg post => exists v, msg = GetResp v /\
                                            impl_status post = Valid /\
                                            impl_value post = v).

      Definition cpSetResp: PMsg SingleValueMsg ImplState :=
        Pmsg cpSetRespM T
             (fun st _ => {| msg_id := ecSetRespM;
                             msg_content := SetResp |} :: nil)
             (fun pre msg post => msg = SetResp /\
                                  impl_status post = Valid /\
                                  impl_value post = impl_value_trs pre).

      Definition pcInvReq: PMsg SingleValueMsg ImplState :=
        Pmsg pcInvReqM
             (fun st => impl_status st = Valid)
             (fun st _ => {| msg_id := pcInvRespM;
                             msg_content := InvResp (impl_value st) |} :: nil)
             (fun pre msg post => msg = InvReq /\ impl_status post = Invalid).

      Definition child: Object SingleValueMsg ImplState :=
        {| obj_idx := childIdx;
           obj_state_init := {| impl_status := Invalid;
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

      Definition cpGetReqValid childIdx: PMsg SingleValueMsg ImplState :=
        Pmsg (cpGetReqM childIdx)
             (fun st => impl_status st = Valid)
             (fun st _ => {| msg_id := cpGetRespM childIdx;
                             msg_content := GetResp (impl_value st) |} :: nil)
             (fun pre msg post => msg = GetReq /\ impl_status post = Invalid).
      
      Definition cpGetReqInvalid childIdx: PMsg SingleValueMsg ImplState :=
        Pmsg (cpGetReqM childIdx)
             (fun st => impl_status st = Invalid)
             (fun st _ => {| msg_id := pcInvReqM childIdx;
                             msg_content := InvReq |} :: nil)
             (fun pre msg post => msg = GetReq /\ impl_status post = Transient).

      Definition cpSetReqValid childIdx: PMsg SingleValueMsg ImplState :=
        Pmsg (cpSetReqM childIdx)
             (fun st => impl_status st = Valid)
             (fun st _ => {| msg_id := cpSetRespM childIdx;
                             msg_content := SetResp |} :: nil)
             (fun pre msg post => exists v, msg = SetReq v /\
                                            impl_status post = Invalid).
      Definition cpSetReqInvalid childIdx: PMsg SingleValueMsg ImplState :=
        Pmsg (cpSetReqM childIdx)
             (fun st => impl_status st = Invalid)
             (fun st _ => {| msg_id := pcInvReqM childIdx;
                             msg_content := InvReq |} :: nil)
             (fun pre msg post => exists v, msg = SetReq v /\
                                            impl_status post = Transient).

      Definition pcInvRespGet childIdx: PMsg SingleValueMsg ImplState :=
        Pmsg (pcInvRespM childIdx)
             (fun st => impl_status st = GetWait)
             (fun st msg =>
                match msg with
                | InvResp v => {| msg_id := cpGetRespM childIdx;
                                  msg_content := GetResp v |} :: nil
                | _ => nil
                end)
             (fun pre msg post => exists v, msg = InvResp v /\
                                            impl_status post = Invalid).
      Definition pcInvRespSet childIdx: PMsg SingleValueMsg ImplState :=
        Pmsg (pcInvRespM childIdx)
             (fun st => impl_status st = SetWait)
             (fun st _ => {| msg_id := cpSetRespM childIdx;
                             msg_content := SetResp |} :: nil)
             (fun pre msg post => exists v, msg = InvResp v /\
                                            impl_status post = Invalid).

      Definition parent : Object SingleValueMsg ImplState :=
        {| obj_idx := parentIdx;
           obj_state_init := {| impl_status := Valid;
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

    Definition impl : System SingleValueMsg ImplState :=
      parent :: (child child1Idx) :: (child child2Idx) :: nil.

  End Impl.

End System.

