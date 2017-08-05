Require Import List String Peano_dec.
Require Import FnMap Language.

Set Implicit Arguments.

Open Scope list.

Inductive SingleValueMsgType :=
| SvmGet
| SvmSet
| SvmInv.

Definition svm_dec: forall m1 m2: SingleValueMsgType, {m1 = m2} + {m1 <> m2}.
Proof.
  decide equality.
Defined.

Inductive SingleValueMsg : SingleValueMsgType -> RqRs -> Set :=
| GetReq : SingleValueMsg SvmGet Rq
| GetResp (v: nat) : SingleValueMsg SvmGet Rs
| SetReq (v: nat) : SingleValueMsg SvmSet Rq
| SetResp : SingleValueMsg SvmSet Rs
| InvReq : SingleValueMsg SvmInv Rq
| InvResp (v: nat) : SingleValueMsg SvmInv Rs.

Notation "'T'" := (fun _ => True).
Notation "'TT'" := (fun pre _ post => pre = post).

Section System.
  Variables extIdx1 extIdx2: nat.

  Section Spec.

    Definition specIdx := 0.
    Definition SpecState := nat. (* a single value *)

    Section PerExt.
      Variable extIdx: nat.

      Definition getReqM := buildMsgId extIdx specIdx SvmGet Rq.
      Definition getRespM := buildMsgId extIdx specIdx SvmGet Rs.
      Definition setReqM := buildMsgId extIdx specIdx SvmSet Rq.
      Definition setRespM := buildMsgId extIdx specIdx SvmSet Rs.

      Definition specGetReq: PMsg SingleValueMsg SpecState :=
        {| pmsg_mid := getReqM;
           pmsg_precond := T;
           pmsg_outs :=
             fun st _ => {| msg_id := getRespM; msg_value := GetResp st |} :: nil;
           pmsg_postcond :=
             fun pre msg post => pre = post
        |}.

      Definition specSetReq: PMsg SingleValueMsg SpecState :=
        {| pmsg_mid := setReqM;
           pmsg_precond := T;
           pmsg_outs :=
             fun st _ => {| msg_id := setRespM; msg_value := SetResp |} :: nil;
           pmsg_postcond :=
             fun pre (msg : SingleValueMsg (msg_type setReqM) (msg_rqrs setReqM)) post =>
               exists v : nat, msg = SetReq v /\ post = v
        |}.

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

      Definition ecGetReqM := buildMsgId (getExtIdx childIdx) childIdx SvmGet Rq.
      Definition ecGetRespM := buildMsgId (getExtIdx childIdx) childIdx SvmGet Rs.
      Definition ecSetReqM := buildMsgId (getExtIdx childIdx) childIdx SvmSet Rq.
      Definition ecSetRespM := buildMsgId (getExtIdx childIdx) childIdx SvmSet Rs.
      Definition cpGetReqM := buildMsgId childIdx parentIdx SvmGet Rq.
      Definition cpGetRespM := buildMsgId childIdx parentIdx SvmGet Rs.
      Definition cpSetReqM := buildMsgId childIdx parentIdx SvmSet Rq.
      Definition cpSetRespM := buildMsgId childIdx parentIdx SvmSet Rs.
      Definition pcInvReqM := buildMsgId parentIdx childIdx SvmInv Rq.
      Definition pcInvRespM := buildMsgId parentIdx childIdx SvmInv Rs.

      Definition ecGetReqValid: PMsg SingleValueMsg ImplState :=
        {| pmsg_mid := ecGetReqM;
           pmsg_precond := fun st => impl_status st = Valid;
           pmsg_outs :=
             fun st _ => {| msg_id := ecGetRespM;
                            msg_value := GetResp (impl_value st) |} :: nil;
           pmsg_postcond :=
             fun pre (msg: SingleValueMsg (msg_type ecGetReqM) (msg_rqrs ecGetReqM)) post =>
               msg = GetReq /\ pre = post
        |}.
      
      Definition ecGetReqInvalid: PMsg SingleValueMsg ImplState :=
        {| pmsg_mid := ecGetReqM;
           pmsg_precond := fun st => impl_status st = Invalid;
           pmsg_outs :=
             fun st _ => {| msg_id := cpGetReqM;
                            msg_value := GetReq |} :: nil;
           pmsg_postcond :=
             fun pre (msg: SingleValueMsg (msg_type ecGetReqM) (msg_rqrs ecGetReqM)) post =>
               msg = GetReq /\ impl_status post = Transient
      |}.

      Definition ecSetReqValid: PMsg SingleValueMsg ImplState :=
        {| pmsg_mid := ecSetReqM;
           pmsg_precond := fun st => impl_status st = Valid;
           pmsg_outs :=
             fun st _ => {| msg_id := ecSetRespM;
                            msg_value := SetResp |} :: nil;
           pmsg_postcond :=
             fun pre (msg: SingleValueMsg (msg_type ecSetReqM) (msg_rqrs ecSetReqM)) post =>
               exists v, msg = SetReq v /\
                         impl_status post = Valid /\
                         impl_value post = v
        |}.

      Definition ecSetReqInvalid: PMsg SingleValueMsg ImplState :=
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
             fun pre (msg: SingleValueMsg (msg_type ecSetReqM) (msg_rqrs ecSetReqM)) post =>
               exists v, msg = SetReq v /\
                         impl_status post = Transient /\
                         impl_value_trs post = v
        |}.

      Definition cpGetResp: PMsg SingleValueMsg ImplState :=
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
             fun pre (msg: SingleValueMsg (msg_type cpGetRespM) (msg_rqrs cpGetRespM)) post =>
               exists v, msg = GetResp v /\
                         impl_status post = Valid /\
                         impl_value post = v
        |}.

      Definition cpSetResp: PMsg SingleValueMsg ImplState :=
        {| pmsg_mid := cpSetRespM;
           pmsg_precond := T;
           pmsg_outs :=
             fun st _ => {| msg_id := ecSetRespM;
                            msg_value := SetResp |} :: nil;
           pmsg_postcond :=
             fun pre (msg: SingleValueMsg (msg_type cpSetRespM) (msg_rqrs cpSetRespM)) post =>
               msg = SetResp /\
               impl_status post = Valid /\
               impl_value post = impl_value_trs pre
        |}.

      Definition pcInvReq: PMsg SingleValueMsg ImplState :=
        {| pmsg_mid := pcInvReqM;
           pmsg_precond := fun st => impl_status st = Valid;
           pmsg_outs :=
             fun st _ => {| msg_id := pcInvRespM;
                            msg_value := InvResp (impl_value st) |} :: nil;
           pmsg_postcond :=
             fun pre (msg: SingleValueMsg (msg_type pcInvReqM) (msg_rqrs pcInvReqM)) post =>
               msg = InvReq /\ impl_status post = Invalid
        |}.

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
        {| pmsg_mid := cpGetReqM childIdx;
           pmsg_precond := fun st => impl_status st = Valid;
           pmsg_outs :=
             fun st _ => {| msg_id := cpGetRespM childIdx;
                            msg_value := GetResp (impl_value st) |} :: nil;
           pmsg_postcond :=
             fun pre (msg: SingleValueMsg (msg_type (cpGetReqM childIdx))
                                          (msg_rqrs (cpGetReqM childIdx))) post =>
               msg = GetReq /\ impl_status post = Invalid
        |}.
      
      Definition cpGetReqInvalid childIdx: PMsg SingleValueMsg ImplState :=
        {| pmsg_mid := cpGetReqM childIdx;
           pmsg_precond := fun st => impl_status st = Invalid;
           pmsg_outs :=
             fun st _ => {| msg_id := pcInvReqM childIdx;
                            msg_value := InvReq |} :: nil;
           pmsg_postcond :=
             fun pre (msg: SingleValueMsg (msg_type (cpGetReqM childIdx))
                                          (msg_rqrs (cpGetReqM childIdx))) post =>
               msg = GetReq /\ impl_status post = Transient
        |}.

      Definition cpSetReqValid childIdx: PMsg SingleValueMsg ImplState :=
        {| pmsg_mid := cpSetReqM childIdx;
           pmsg_precond := fun st => impl_status st = Valid;
           pmsg_outs :=
             fun st _ => {| msg_id := cpSetRespM childIdx;
                            msg_value := SetResp |} :: nil;
           pmsg_postcond :=
             fun pre (msg: SingleValueMsg (msg_type (cpSetReqM childIdx))
                                          (msg_rqrs (cpSetReqM childIdx))) post =>
               exists v, msg = SetReq v /\
                         impl_status post = Invalid
        |}.
      
      Definition cpSetReqInvalid childIdx: PMsg SingleValueMsg ImplState :=
        {| pmsg_mid := cpSetReqM childIdx;
           pmsg_precond := fun st => impl_status st = Invalid;
           pmsg_outs :=
             fun st _ => {| msg_id := pcInvReqM childIdx;
                            msg_value := InvReq |} :: nil;
           pmsg_postcond :=
             fun pre (msg: SingleValueMsg (msg_type (cpSetReqM childIdx))
                                          (msg_rqrs (cpSetReqM childIdx))) post =>
               exists v, msg = SetReq v /\
                         impl_status post = Transient
        |}.

      Definition pcInvRespGet childIdx: PMsg SingleValueMsg ImplState :=
        {| pmsg_mid := pcInvRespM childIdx;
           pmsg_precond := fun st => impl_status st = GetWait;
           pmsg_outs :=
             fun st msg =>
               match msg with
               | InvResp v => {| msg_id := cpGetRespM childIdx;
                                 msg_value := GetResp v |} :: nil
               | _ => nil
               end;
           pmsg_postcond :=
             fun pre (msg: SingleValueMsg (msg_type (pcInvRespM childIdx))
                                          (msg_rqrs (pcInvRespM childIdx))) post =>
               exists v, msg = InvResp v /\
                         impl_status post = Invalid
        |}.
      
      Definition pcInvRespSet childIdx: PMsg SingleValueMsg ImplState :=
        {| pmsg_mid := pcInvRespM childIdx;
           pmsg_precond := fun st => impl_status st = SetWait;
           pmsg_outs :=
             fun st _ => {| msg_id := cpSetRespM childIdx;
                            msg_value := SetResp |} :: nil;
           pmsg_postcond :=
             fun pre (msg: SingleValueMsg (msg_type (pcInvRespM childIdx))
                                          (msg_rqrs (pcInvRespM childIdx))) post =>
               exists v, msg = InvResp v /\
                         impl_status post = Invalid
        |}.

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

