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

Section System.
  Variables extIdx1 extIdx2: nat.

  Section Spec.

    Definition SpecState := nat. (* a single value *)
    Definition specIdx := 0.

    Definition specGetResp eidx v : PMsg SingleValueMsg SpecState :=
      PmExtOut _ (buildMsgId eidx specIdx Rs (GetResp v)).
    Definition specGetReq eidx : PMsg SingleValueMsg SpecState :=
      PmIn (buildMsgId eidx specIdx Rq GetReq)
           T (fun st => (specGetResp eidx st) :: nil) T.

    Definition specSetResp eidx : PMsg SingleValueMsg SpecState :=
      PmExtOut _ (buildMsgId eidx specIdx Rs SetResp).
    Definition specSetReq eidx v : PMsg SingleValueMsg SpecState :=
      PmIn (buildMsgId eidx specIdx Rq (SetReq v))
           T (fun st => (specSetResp eidx) :: nil)
           (fun st => st = v).

    Definition specSingleton : Object SingleValueMsg SpecState :=
      {| obj_idx := 0;
         obj_state_init := 0;
         obj_exts_allowed :=
           fun msg =>
             (exists v, msg = (midOf (specGetResp extIdx1 v))) \/
             (msg = midOf (specGetReq extIdx1)) \/
             (msg = midOf (specSetResp extIdx1)) \/
             (exists v, msg = (midOf (specSetReq extIdx1 v))) \/
             (exists v, msg = (midOf (specGetResp extIdx2 v))) \/
             (msg = midOf (specGetReq extIdx2)) \/
             (msg = midOf (specSetResp extIdx2)) \/
             (exists v, msg = (midOf (specSetReq extIdx2 v)))
      |}.

    Definition spec : Objects SingleValueMsg SpecState :=
      specSingleton :: nil.

  End Spec.

  Section Impl.

    Inductive ValStatus := Invalid | Transient | Valid.

    Record ImplState :=
      { impl_status : ValStatus;
        impl_value : nat
      }.

    Definition parentIdx := 0.
    Definition child1Idx := 1.
    Definition child2Idx := 2.
    Definition theOtherChild (idx: nat) :=
      if eq_nat_dec idx child1Idx then child2Idx else child1Idx.
    Definition getExtIdx (idx: nat) :=
      if eq_nat_dec idx child1Idx then extIdx1 else extIdx2.

    Section Messages.

      Definition ecGetResp childIdx v : PMsg SingleValueMsg ImplState :=
        PmExtOut _ (buildMsgId (getExtIdx childIdx) childIdx Rs (GetResp v)).

      Definition cpGetResp childIdx v : PMsg SingleValueMsg ImplState :=
        PmIn (buildMsgId childIdx parentIdx Rs (GetResp v))
             T
             (fun st => (ecGetResp childIdx v) :: nil)
             (fun st => impl_status st = Valid /\
                        impl_value st = v).

      Definition pcInvResp childIdx v : PMsg SingleValueMsg ImplState :=
        PmIn (buildMsgId parentIdx childIdx Rs (InvResp v))
             T
             (fun st => (cpGetResp (theOtherChild childIdx) v) :: nil)
             (fun st => impl_status st = Invalid).

      Definition pcInvReq childIdx : PMsg SingleValueMsg ImplState :=
        PmIn (buildMsgId parentIdx childIdx Rq InvReq)
             (fun st => impl_status st = Valid)
             (fun st => (pcInvResp childIdx (impl_value st)) :: nil)
             (fun st => impl_status st = Invalid).

      Definition cpGetReqValid childIdx : PMsg SingleValueMsg ImplState :=
        PmIn (buildMsgId childIdx parentIdx Rq GetReq)
             (fun st => impl_status st = Valid)
             (fun st => (cpGetResp childIdx (impl_value st)) :: nil)
             (fun st => impl_status st = Invalid).

      Definition cpGetReqInvalid childIdx : PMsg SingleValueMsg ImplState :=
        PmIn (buildMsgId childIdx parentIdx Rq GetReq)
             (fun st => impl_status st = Invalid)
             (fun st => (pcInvReq (theOtherChild childIdx)) :: nil)
             (fun st => impl_status st = Transient).

      Definition ecGetReqValid childIdx : PMsg SingleValueMsg ImplState :=
        PmIn (buildMsgId (getExtIdx childIdx) childIdx Rq GetReq)
             (fun st => impl_status st = Valid)
             (fun st => (ecGetResp childIdx (impl_value st)) :: nil)
             (fun st => True).

      (* TODO: a child doesn't know the state of parent, so it should send
       * all possible predicated messages for each precondition, which is weird.
       *)
      Definition ecGetReqInvalid childIdx : PMsg SingleValueMsg ImplState :=
        PmIn (buildMsgId (getExtIdx childIdx) childIdx Rq GetReq)
             (fun st => impl_status st = Invalid)
             (fun st => (cpGetReqInvalid childIdx) :: (cpGetReqValid childIdx) :: nil)
             (fun st => impl_status st = Transient).

      (* TODO: for "set" requests/responses, we may need "prestate" 
       * to state postconditions.
       *)
      
    End Messages.

    Definition parent : Object SingleValueMsg ImplState :=
      {| obj_idx := parentIdx;
         obj_state_init := {| impl_status := Valid;
                              impl_value := 0 |};
         obj_exts_allowed := fun _ => False
      |}.

    Definition child childIdx : Object SingleValueMsg ImplState :=
      {| obj_idx := childIdx;
         obj_state_init := {| impl_status := Invalid;
                              impl_value := 0 |};
         obj_exts_allowed := fun msg => True (* TODO *)
      |}.

    Definition impl : Objects SingleValueMsg ImplState :=
      parent :: (child child1Idx) :: (child child2Idx) :: nil.

  End Impl.

End System.

