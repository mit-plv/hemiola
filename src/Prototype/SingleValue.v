Require Import List String Peano_dec.
Require Import Language.

Set Implicit Arguments.

Open Scope list.

Inductive SingleValueMsg : MsgType -> Set :=
(* external *)
| SvmGetReq : SingleValueMsg Req
| SvmGetResp (v: nat) : SingleValueMsg Resp
| SvmSetReq (v: nat) : SingleValueMsg Req
| SvmSetResp : SingleValueMsg Resp
(* internal *)
| SvmInvReq : SingleValueMsg Req
| SvmInvResp (v: nat) : SingleValueMsg Resp.

Section Spec.

  Definition SpecState := nat. (* a single value *)
  Definition specIdx := 0.

  Definition SpecGetReq : RuleT SingleValueMsg SpecState :=
    fun msg =>
      match msg_content msg, msg_type msg with
      | SvmGetReq, Req => fun st => Some ((buildMsg _ specIdx (msg_from msg)
                                                    (SvmGetResp st)) :: nil, st)
      | _, _ => fun _ => None
      end.

  Definition SpecSetReq : RuleT SingleValueMsg SpecState :=
    fun msg =>
      match msg_content msg, msg_type msg with
      | SvmSetReq v, Req => fun _ => Some ((buildMsg _ specIdx (msg_from msg)
                                                     SvmSetResp) :: nil, v)
      | _, _ => fun _ => None
      end.

  Definition singleton : Object SingleValueMsg SpecState :=
    {| obj_idx := 0;
       obj_state_init := 0;
       obj_rules := SpecGetReq :: SpecSetReq :: nil |}.

  Definition spec : Objects SingleValueMsg :=
    (existT (fun st => Object SingleValueMsg st) SpecState singleton)
      :: nil.

End Spec.

Section Impl.

  Record ParentState :=
    { ps_is_valid : bool;
      ps_value : nat;
      ps_request_from : option (IdxT * bool) (* is_get *)
    }.
  Record ChildState :=
    { cs_is_valid : bool;
      cs_value : nat;
      cs_request_from : option (IdxT * nat) }.

  Definition parentIdx := 0.
  Definition child1Idx := 1.
  Definition child2Idx := 2.
  Definition implIndices := parentIdx :: child1Idx :: child2Idx :: nil.
  Definition childrenIndices := child1Idx :: child2Idx :: nil.
  Definition from_external (i: IdxT) :=
    if in_dec eq_nat_dec i implIndices then false else true.
  Definition from_children (i: IdxT) :=
    if eq_nat_dec i child1Idx then true
    else if eq_nat_dec i child2Idx then true else false.

  Definition theOtherChild (idx: nat) :=
    if eq_nat_dec idx child1Idx then child2Idx else child1Idx.

  Section Parent.

    (* All messages are from children. *)

    Definition ParentGetReq : RuleT SingleValueMsg ParentState :=
      fun msg =>
        if from_children (msg_from msg)
        then
          match msg_content msg, msg_type msg with
          | SvmGetReq, Req =>
            fun st =>
              match ps_request_from st with
              | Some _ => None
              | None => if ps_is_valid st
                        then Some ((buildMsg _ parentIdx (msg_from msg)
                                             (SvmGetResp (ps_value st))) :: nil,
                                   {| ps_is_valid := false;
                                      ps_value := ps_value st;
                                      ps_request_from := ps_request_from st |})
                        else Some ((buildMsg _ parentIdx (theOtherChild (msg_from msg))
                                             SvmInvReq) :: nil,
                                   {| ps_is_valid := ps_is_valid st;
                                      ps_value := ps_value st;
                                      ps_request_from := Some (msg_from msg, true) |})
              end
          | _, _ => fun _ => None
          end
        else fun _ => None.

    Definition ParentSetReq : RuleT SingleValueMsg ParentState :=
      fun msg =>
        if from_children (msg_from msg) then
          match msg_content msg, msg_type msg with
          | SvmSetReq _, Req =>
            fun st =>
              match ps_request_from st with
              | Some _ => None
              | None => if ps_is_valid st
                        then Some ((buildMsg _ parentIdx (msg_from msg) SvmSetResp) :: nil,
                                   {| ps_is_valid := false;
                                      ps_value := ps_value st;
                                      ps_request_from := ps_request_from st |})
                        else Some ((buildMsg _ parentIdx (theOtherChild (msg_from msg))
                                             SvmInvReq) :: nil,
                                   {| ps_is_valid := ps_is_valid st;
                                      ps_value := ps_value st;
                                      ps_request_from := Some (msg_from msg, false) |})
              end
          | _, _ => fun _ => None
          end
        else fun _ => None.

    Definition ParentInvResp : RuleT SingleValueMsg ParentState :=
      fun msg =>
        if from_children (msg_from msg) then
          match msg_content msg, msg_type msg with
          | SvmInvResp v, Resp =>
            fun st =>
              match ps_request_from st with
              | None => None
              | Some (childTo, is_get) =>
                Some ((buildMsg _ parentIdx childTo
                                (if is_get then SvmGetResp v else SvmSetResp)) :: nil,
                      {| ps_is_valid := ps_is_valid st;
                         ps_value := ps_value st;
                         ps_request_from := None |})
              end
          | _, _ => fun _ => None
          end
        else fun _ => None.

    Definition parent : Object SingleValueMsg ParentState :=
      {| obj_idx := parentIdx;
         obj_state_init := {| ps_is_valid := true;
                              ps_value := 0;
                              ps_request_from := None |};
         obj_rules := ParentGetReq :: ParentSetReq :: ParentInvResp :: nil |}.

  End Parent.

  Section Child.
    Variable childIdx : nat.

    (* from external *)
    Definition ChildGetReq : RuleT SingleValueMsg ChildState :=
      fun msg =>
        if from_external (msg_from msg) then
          match msg_content msg, msg_type msg with
          | SvmGetReq, Req =>
            fun st =>
              match cs_request_from st with
              | Some _ => None
              | None =>
                if cs_is_valid st
                then Some ((buildMsg _ childIdx (msg_from msg)
                                     (SvmGetResp (cs_value st))) :: nil,
                           st)
                else Some ((buildMsg _ childIdx parentIdx SvmGetReq) :: nil,
                           {| cs_is_valid := cs_is_valid st;
                              cs_value := cs_value st;
                              cs_request_from := Some (msg_from msg, O) |})
              end
          | _, _ => fun _ => None
          end
        else fun _ => None.

    (* from the parent *)
    Definition ChildGetResp : RuleT SingleValueMsg ChildState :=
      fun msg =>
        if from_external (msg_from msg) then fun _ => None
        else
          match msg_content msg, msg_type msg with
          | SvmGetResp v, Resp =>
            fun st =>
              match cs_request_from st with
              | None => None
              | Some (efrom, _) =>
                Some ((buildMsg _ childIdx efrom (SvmGetResp v)) :: nil,
                      {| cs_is_valid := true;
                         cs_value := v;
                         cs_request_from := None |})
              end
          | _, _ => fun _ => None
          end.

    (* from external *)
    Definition ChildSetReq : RuleT SingleValueMsg ChildState :=
      fun msg =>
        if from_external (msg_from msg) then
          match msg_content msg, msg_type msg with
          | SvmSetReq v, Req =>
            fun st =>
              match cs_request_from st with
              | Some _ => None
              | None =>
                if cs_is_valid st
                then Some ((buildMsg _ childIdx (msg_from msg)
                                     SvmSetResp) :: nil,
                           {| cs_is_valid := cs_is_valid st;
                              cs_value := v;
                              cs_request_from := cs_request_from st |})
                else Some ((buildMsg _ childIdx parentIdx (SvmSetReq v)) :: nil,
                           {| cs_is_valid := cs_is_valid st;
                              cs_value := cs_value st;
                              cs_request_from := Some (msg_from msg, v) |})
              end
          | _, _ => fun _ => None
          end
        else fun _ => None.

    (* from the parent *)
    Definition ChildSetResp : RuleT SingleValueMsg ChildState :=
      fun msg =>
        if from_external (msg_from msg) then fun _ => None
        else
          match msg_content msg, msg_type msg with
          | SvmSetResp, Resp =>
            fun st =>
              match cs_request_from st with
              | None => None
              | Some (efrom, v) =>
                Some ((buildMsg _ childIdx efrom SvmSetResp) :: nil,
                      {| cs_is_valid := true;
                         cs_value := v;
                         cs_request_from := None |})
              end
          | _, _ => fun _ => None
          end.

    (* from the parent *)
    Definition ChildInvReq : RuleT SingleValueMsg ChildState :=
      fun msg =>
        if from_external (msg_from msg) then fun _ => None
        else
          match msg_content msg, msg_type msg with
          | SvmInvReq, Req =>
            fun st =>
              if cs_is_valid st then
                Some ((buildMsg _ childIdx parentIdx
                                (SvmInvResp (cs_value st))) :: nil,
                      {| cs_is_valid := false;
                         cs_value := cs_value st;
                         cs_request_from := cs_request_from st |})
              else None
          | _, _ => fun _ => None
          end.

    Definition child : Object SingleValueMsg ChildState :=
      {| obj_idx := childIdx;
         obj_state_init := {| cs_is_valid := false;
                              cs_value := 0;
                              cs_request_from := None |};
         obj_rules := ChildGetReq :: ChildGetResp :: ChildSetReq :: ChildSetResp
                                  :: ChildInvReq :: nil |}.

  End Child.

  Definition impl : Objects SingleValueMsg :=
    (existT (fun st => Object SingleValueMsg st) _ parent)
      :: (existT (fun st => Object SingleValueMsg st) _ (child child1Idx))
      :: (existT (fun st => Object SingleValueMsg st) _ (child child2Idx))
      :: nil.

End Impl.

