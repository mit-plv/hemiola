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
Notation "'TT'" := (fun pre post => pre = post).

Section System.
  Variables extIdx1 extIdx2: nat.

  Section Spec.

    Definition SpecState := nat. (* a single value *)
    Definition specIdx := 0.

    Definition specGetReq eidx : PMsg SingleValueMsg SpecState :=
      Pmsg (buildMsgId eidx specIdx Rq GetReq)
           T (fun st => (buildMsgId eidx specIdx Rs (GetResp st)) :: nil) TT.

    Definition specSetReq eidx v : PMsg SingleValueMsg SpecState :=
      Pmsg (buildMsgId eidx specIdx Rq (SetReq v))
           T (fun st => (buildMsgId eidx specIdx Rs SetResp) :: nil)
           (fun _ st => st = v).

    Definition specSingleton : Object SingleValueMsg SpecState :=
      {| obj_idx := 0;
         obj_state_init := 0;
         obj_pmsg_ints := fun _ => False;
         obj_pmsg_exts := 
           fun msg =>
             (msg = specGetReq extIdx1) \/
             (exists v, msg = specSetReq extIdx1 v) \/
             (msg = specGetReq extIdx2) \/
             (exists v, msg = specSetReq extIdx2 v)
      |}.

    Definition spec : Objects SingleValueMsg SpecState :=
      specSingleton :: nil.

  End Spec.

  Section Impl.

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

    Definition parentIdx := 0.
    Definition child1Idx := 1.
    Definition child2Idx := 2.
    Definition theOtherChild (idx: nat) :=
      if eq_nat_dec idx child1Idx then child2Idx else child1Idx.
    Definition getExtIdx (idx: nat) :=
      if eq_nat_dec idx child1Idx then extIdx1 else extIdx2.

    Section Child.
      Variable childIdx: nat.

      Definition ecGetReqM := buildMsgId (getExtIdx childIdx) childIdx Rq GetReq.
      Definition ecGetRespM v := buildMsgId (getExtIdx childIdx) childIdx Rs (GetResp v).
      Definition ecSetReqM v := buildMsgId (getExtIdx childIdx) childIdx Rq (SetReq v).
      Definition ecSetRespM := buildMsgId (getExtIdx childIdx) childIdx Rs SetResp.
      Definition cpGetReqM := buildMsgId childIdx parentIdx Rq GetReq.
      Definition cpGetRespM v := buildMsgId childIdx parentIdx Rs (GetResp v).
      Definition cpSetReqM v := buildMsgId childIdx parentIdx Rq (SetReq v).
      Definition cpSetRespM := buildMsgId childIdx parentIdx Rs SetResp.
      Definition pcInvReqM := buildMsgId parentIdx childIdx Rq InvReq.
      Definition pcInvRespM v := buildMsgId parentIdx childIdx Rs (InvResp v).

      Definition ecGetReqValid: PMsg SingleValueMsg ImplState :=
        Pmsg ecGetReqM
             (fun st => impl_status st = Valid)
             (fun st => ecGetRespM (impl_value st) :: nil)
             TT.
      
      Definition ecGetReqInvalid: PMsg SingleValueMsg ImplState :=
        Pmsg ecGetReqM
             (fun st => impl_status st = Invalid)
             (fun st => cpGetReqM :: nil)
             (fun pre post => impl_status post = Transient).

      Definition ecSetReqValid v: PMsg SingleValueMsg ImplState :=
        Pmsg (ecSetReqM v)
             (fun st => impl_status st = Valid)
             (fun st => ecSetRespM :: nil)
             (fun pre post => impl_status post = Valid /\
                              impl_value post = v).

      Definition ecSetReqInvalid v: PMsg SingleValueMsg ImplState :=
        Pmsg (ecSetReqM v)
             (fun st => impl_status st = Invalid)
             (fun st => cpSetReqM v :: nil)
             (fun pre post => impl_status post = Transient /\
                              impl_value_trs post = v).

      Definition cpGetResp v: PMsg SingleValueMsg ImplState :=
        Pmsg (cpGetRespM v)
             T
             (fun st => ecGetRespM v :: nil)
             (fun pre post => impl_status post = Valid /\
                              impl_value post = v).

      Definition cpSetResp: PMsg SingleValueMsg ImplState :=
        Pmsg cpSetRespM
             T
             (fun st => ecSetRespM :: nil)
             (fun pre post => impl_status post = Valid /\
                              impl_value post = impl_value_trs pre).

      Definition pcInvReq: PMsg SingleValueMsg ImplState :=
        Pmsg pcInvReqM
             (fun st => impl_status st = Valid)
             (fun st => pcInvRespM (impl_value st) :: nil)
             (fun pre post => impl_status post = Invalid).

      Definition child: Object SingleValueMsg ImplState :=
        {| obj_idx := childIdx;
           obj_state_init := {| impl_status := Invalid;
                                impl_value_trs := 0;
                                impl_value := 0 |};
           obj_pmsg_ints := fun msg =>
                              (exists v, msg = cpGetResp v) \/
                              (msg = cpSetResp) \/
                              (msg = pcInvReq);
           obj_pmsg_exts := fun msg =>
                              (msg = ecGetReqValid) \/
                              (msg = ecGetReqInvalid) \/
                              (exists v, msg = ecSetReqValid v) \/
                              (exists v, msg = ecSetReqInvalid v)
        |}.

    End Child.

    Section Parent.

      Definition cpGetReqValid childIdx: PMsg SingleValueMsg ImplState :=
        Pmsg (cpGetReqM childIdx)
             (fun st => impl_status st = Valid)
             (fun st => cpGetRespM childIdx (impl_value st) :: nil)
             (fun pre post => impl_status post = Invalid).
      Definition cpGetReqInvalid childIdx: PMsg SingleValueMsg ImplState :=
        Pmsg (cpGetReqM childIdx)
             (fun st => impl_status st = Invalid)
             (fun st => pcInvReqM childIdx :: nil)
             (fun pre post => impl_status post = Transient).

      Definition cpSetReqValid childIdx v: PMsg SingleValueMsg ImplState :=
        Pmsg (cpSetReqM childIdx v)
             (fun st => impl_status st = Valid)
             (fun st => cpSetRespM childIdx :: nil)
             (fun pre post => impl_status post = Invalid).
      Definition cpSetReqInvalid childIdx v: PMsg SingleValueMsg ImplState :=
        Pmsg (cpSetReqM childIdx v)
             (fun st => impl_status st = Invalid)
             (fun st => pcInvReqM childIdx :: nil)
             (fun pre post => impl_status post = Transient).

      Definition pcInvRespGet childIdx v: PMsg SingleValueMsg ImplState :=
        Pmsg (pcInvRespM childIdx v)
             (fun st => impl_status st = GetWait)
             (fun st => cpGetRespM childIdx v :: nil)
             (fun pre post => impl_status post = Invalid).
      Definition pcInvRespSet childIdx v: PMsg SingleValueMsg ImplState :=
        Pmsg (pcInvRespM childIdx v)
             (fun st => impl_status st = SetWait)
             (fun st => cpSetRespM childIdx :: nil)
             (fun pre post => impl_status post = Invalid).

      Definition parent : Object SingleValueMsg ImplState :=
        {| obj_idx := parentIdx;
           obj_state_init := {| impl_status := Valid;
                                impl_value_trs := 0;
                                impl_value := 0 |};
           obj_pmsg_ints := fun msg =>
                              (msg = cpGetReqValid child1Idx) \/
                              (msg = cpGetReqInvalid child1Idx) \/
                              (exists v, msg = cpSetReqValid child1Idx v) \/
                              (exists v, msg = cpSetReqInvalid child1Idx v) \/
                              (exists v, msg = pcInvRespGet child1Idx v) \/
                              (exists v, msg = pcInvRespSet child1Idx v) \/
                              (msg = cpGetReqValid child2Idx) \/
                              (msg = cpGetReqInvalid child2Idx) \/
                              (exists v, msg = cpSetReqValid child2Idx v) \/
                              (exists v, msg = cpSetReqInvalid child2Idx v) \/
                              (exists v, msg = pcInvRespGet child2Idx v) \/
                              (exists v, msg = pcInvRespSet child2Idx v);
           obj_pmsg_exts := fun _ => False
        |}.

    End Parent.

    Definition impl : Objects SingleValueMsg ImplState :=
      parent :: (child child1Idx) :: (child child2Idx) :: nil.

  End Impl.

End System.

