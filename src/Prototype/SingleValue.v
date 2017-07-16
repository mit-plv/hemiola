Require Import List String Peano_dec.
Require Import FnMap Language.

Set Implicit Arguments.

Open Scope list.

Inductive SingleValueMsg : MsgType -> Set :=
(* external *)
| GetReq : SingleValueMsg Rq
| GetResp (v: nat) : SingleValueMsg Rs
| SetReq (v: nat) : SingleValueMsg Rq
| SetResp : SingleValueMsg Rs
(* internal *)
| InvReq : SingleValueMsg Rq
| InvResp (v: nat) : SingleValueMsg Rs.

Section Spec.

  Definition SpecState := nat. (* a single value *)
  Definition specIdx := 0.

  Definition pmsgGetResp rq rs v : PredMsg SingleValueMsg SpecState :=
    PmRs _ (buildMsg _ rq rs (GetResp v)).
  Definition pmsgSetResp rq rs : PredMsg SingleValueMsg SpecState :=
    PmRs _ (buildMsg _ rq rs SetResp).

  Definition SpecGetReq : Rule SingleValueMsg SpecState :=
    fun msg _ st =>
      match msg_content msg with
      | GetReq => Some ((pmsgGetResp (msg_rq msg) (msg_rs msg) st) :: nil,
                        st)
      | _ => None
      end.

  Definition SpecSetReq : Rule SingleValueMsg SpecState :=
    fun msg _ st =>
      match msg_content msg with
      | SetReq v => Some ((pmsgSetResp (msg_rq msg) (msg_rs msg)) :: nil,
                          v)
      | _ => None
      end.

  Definition singleton : Object SingleValueMsg SpecState :=
    {| obj_idx := 0;
       obj_state_init := 0;
       obj_rules := SpecGetReq :: SpecSetReq :: nil |}.

  Definition spec : Objects SingleValueMsg SpecState :=
    singleton :: nil.

End Spec.

Section Impl.

  Record ImplState :=
    { impl_is_valid : bool;
      impl_value : nat;
    }.

  Definition parentIdx := 0.
  Definition child1Idx := 1.
  Definition child2Idx := 2.
  Definition implIndices := parentIdx :: child1Idx :: child2Idx :: nil.
  Definition from_external (i: IdxT) :=
    if in_dec eq_nat_dec i implIndices then false else true.
  Definition from_children (i: IdxT) :=
    if eq_nat_dec i child1Idx then true
    else if eq_nat_dec i child2Idx then true else false.
  Definition theOtherChild (idx: nat) :=
    if eq_nat_dec idx child1Idx then child2Idx else child1Idx.

  Section PredMsgs.

    Definition pmsgParentGetReq rq rs : PredMsg SingleValueMsg ImplState :=
      PmRq (buildMsg _ rq rs GetReq)
           (Some (TLocked {| le_idx := rq; le_val := O; le_flag := false |}))
           (fun st locks => locks = @empty _ _).
    Definition pmsgParentGetResp rq rs v : PredMsg SingleValueMsg ImplState :=
      PmRs _ (buildMsg _ rq rs (GetResp v)).
    
    Definition pmsgParentSetReq rq rs v : PredMsg SingleValueMsg ImplState :=
      PmRq (buildMsg _ rq rs (SetReq v))
           (Some (TLocked {| le_idx := rq; le_val := v; le_flag := false |}))
           (fun st locks => locks = @empty _ _).
    Definition pmsgParentSetResp rq rs : PredMsg SingleValueMsg ImplState :=
      PmRs _ (buildMsg _ rq rs SetResp).

    Definition pmsgChildGetReq := pmsgParentGetReq.
    Definition pmsgChildGetResp := pmsgParentGetResp.
    Definition pmsgChildSetReq := pmsgParentSetReq.
    Definition pmsgChildSetResp := pmsgParentSetResp.
    Definition pmsgChildInvReq rq rs (is_get: bool) : PredMsg SingleValueMsg ImplState :=
      PmRq (buildMsg _ rq rs InvReq)
           (Some (TLocked {| le_idx := rq; le_val := O; le_flag := is_get |}))
           (fun st locks => impl_is_valid st = true).
    Definition pmsgChildInvResp rq rs v : PredMsg SingleValueMsg ImplState :=
      PmRs _ (buildMsg _ rq rs (InvResp v)).

  End PredMsgs.

  Section Parent.

    (** All messages are from children. *)

    Definition ParentGetReq : Rule SingleValueMsg ImplState :=
      fun msg locks st =>
        if from_children (msg_rq msg) then
          match msg_content msg with
          | GetReq =>
            if impl_is_valid st
            then Some ((pmsgParentGetResp (msg_rq msg) (msg_rs msg) (impl_value st)) :: nil,
                       {| impl_is_valid := false;
                          impl_value := impl_value st |})
            else Some ((pmsgChildInvReq parentIdx (theOtherChild (msg_rq msg)) true) :: nil,
                       {| impl_is_valid := impl_is_valid st;
                          impl_value := impl_value st |})
          | _ => None
          end
        else None.

    Definition ParentSetReq : Rule SingleValueMsg ImplState :=
      fun msg locks st =>
        if from_children (msg_rq msg) then
          match msg_content msg with
          | SetReq _ =>
            if impl_is_valid st
            then Some ((pmsgParentSetResp (msg_rq msg) (msg_rs msg)) :: nil,
                       {| impl_is_valid := false;
                          impl_value := impl_value st |})
            else Some ((pmsgChildInvReq parentIdx (theOtherChild (msg_rq msg)) true) :: nil,
                       {| impl_is_valid := impl_is_valid st;
                          impl_value := impl_value st |})
          | _ => None
          end
        else None.

    Definition ParentInvResp : Rule SingleValueMsg ImplState :=
      fun msg locks st =>
        if from_children (msg_rs msg) then
          match msg_content msg with
          | InvResp v =>
            match find (msg_rq msg, msg_rs msg) locks with
            | Some (TLocked {| le_idx := childTo; le_flag := is_get |}) =>
              Some ((if is_get
                     then pmsgParentGetResp childTo parentIdx v
                     else pmsgParentSetResp childTo parentIdx) :: nil,
                    {| impl_is_valid := impl_is_valid st;
                       impl_value := impl_value st |})
            | _ => None
            end
          | _ => None
          end
        else None.

    Definition parent : Object SingleValueMsg ImplState :=
      {| obj_idx := parentIdx;
         obj_state_init := {| impl_is_valid := true;
                              impl_value := 0 |};
         obj_rules := ParentGetReq :: ParentSetReq :: ParentInvResp :: nil |}.

  End Parent.

  Section Child.
    Variable childIdx : nat.

    (* from external *)
    Definition ChildGetReq : Rule SingleValueMsg ImplState :=
      fun msg locks st =>
        if from_external (msg_rq msg) then
          match msg_content msg with
          | GetReq =>
            if impl_is_valid st
            then Some ((pmsgChildGetResp (msg_rq msg) (msg_rs msg) (impl_value st)) :: nil,
                       st)
            else Some ((pmsgParentGetReq childIdx parentIdx) :: nil,
                       {| impl_is_valid := impl_is_valid st;
                          impl_value := impl_value st |})
          | _ => None
          end
        else None.

    (* from the parent *)
    Definition ChildGetResp : Rule SingleValueMsg ImplState :=
      fun msg locks st =>
        if from_external (msg_rs msg) then None
        else
          match msg_content msg with
          | GetResp v =>
            match find (msg_rq msg, msg_rs msg) locks with
            | Some (TLocked {| le_idx := efrom |}) =>
              Some ((pmsgChildGetResp efrom childIdx v) :: nil,
                    {| impl_is_valid := true;
                       impl_value := v |})
            | _ => None
            end
          | _ => None
          end.

    (* from external *)
    Definition ChildSetReq : Rule SingleValueMsg ImplState :=
      fun msg locks st =>
        if from_external (msg_rq msg) then
          match msg_content msg with
          | SetReq v =>
            if impl_is_valid st
            then Some ((pmsgChildSetResp (msg_rq msg) (msg_rs msg)) :: nil,
                       {| impl_is_valid := impl_is_valid st;
                          impl_value := v |})
            else Some ((pmsgParentSetReq childIdx parentIdx v) :: nil,
                       {| impl_is_valid := impl_is_valid st;
                          impl_value := impl_value st |})
          | _ => None
          end
        else None.

    (* from the parent *)
    Definition ChildSetResp : Rule SingleValueMsg ImplState :=
      fun msg locks st =>
        if from_external (msg_rs msg) then None
        else
          match msg_content msg with
          | SetResp =>
            match find (msg_rq msg, msg_rs msg) locks with
            | Some (TLocked {| le_idx := efrom; le_val := v |}) =>
              Some ((pmsgChildSetResp efrom childIdx) :: nil,
                    {| impl_is_valid := true;
                       impl_value := v |})
            | _ => None
            end
          | _ => None
          end.

    (* from the parent *)
    Definition ChildInvReq : Rule SingleValueMsg ImplState :=
      fun msg locks st =>
        if from_external (msg_rq msg) then None
        else
          match msg_content msg with
          | InvReq =>
            Some ((pmsgChildInvResp (msg_rq msg) (msg_rs msg) (impl_value st)) :: nil,
                  {| impl_is_valid := false;
                     impl_value := impl_value st |})
          | _ => None
          end.

    Definition child : Object SingleValueMsg ImplState :=
      {| obj_idx := childIdx;
         obj_state_init := {| impl_is_valid := false;
                              impl_value := 0 |};
         obj_rules := ChildGetReq :: ChildGetResp :: ChildSetReq :: ChildSetResp
                                  :: ChildInvReq :: nil |}.

  End Child.

  Definition impl : Objects SingleValueMsg ImplState :=
    parent :: (child child1Idx) :: (child child2Idx) :: nil.

End Impl.

