Require Import List String Peano_dec.
Require Import Language.

Set Implicit Arguments.

Open Scope list.

Inductive SingleValueMsg :=
(* external *)
| SvmGetReq
| SvmGetResp (v: nat)
| SvmSetReq (v: nat)
| SvmSetResp
(* internal *)
| SvmInvReq
| SvmInvResp (v: nat).

Definition svm_is_req (svm: SingleValueMsg) :=
  match svm with
  | SvmGetReq
  | SvmSetReq _
  | SvmInvReq => true
  | _ => false
  end.

Section Spec.

  Definition SpecState := nat. (* a single value *)

  Definition SpecGetReq : RuleT SingleValueMsg SpecState :=
    fun imsg =>
      match imsg with
      | (efrom, SvmGetReq) => fun st => Some (nil, Some (efrom, SvmGetResp st), st)
      | _ => fun _ => None
      end.

  Definition SpecSetReq : RuleT SingleValueMsg SpecState :=
    fun imsg =>
      match imsg with
      | (efrom, SvmSetReq v) => fun _ => Some (nil, Some (efrom, SvmSetResp), v)
      | _ => fun _ => None
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

  Definition theOtherChild (idx: nat) :=
    if eq_nat_dec idx child1Idx then child2Idx else child1Idx.

  Section Parent.

    (* All messages are from children. *)

    Definition ParentGetReq : RuleT SingleValueMsg ParentState :=
      fun imsg =>
        match imsg with
        | (efrom, SvmGetReq) =>
          fun st =>
            match ps_request_from st with
            | Some _ => None
            | None => if ps_is_valid st
                      then Some (nil, Some (efrom, SvmGetResp (ps_value st)),
                                 {| ps_is_valid := false;
                                    ps_value := ps_value st;
                                    ps_request_from := ps_request_from st |})
                      else Some ((theOtherChild efrom, SvmInvReq) :: nil, None,
                                 {| ps_is_valid := ps_is_valid st;
                                    ps_value := ps_value st;
                                    ps_request_from := Some (efrom, true) |})
            end
        | _ => fun _ => None
        end.

    Definition ParentSetReq : RuleT SingleValueMsg ParentState :=
      fun imsg =>
        match imsg with
        | (efrom, SvmSetReq _) =>
          fun st =>
            match ps_request_from st with
            | Some _ => None
            | None => if ps_is_valid st
                      then Some (nil, Some (efrom, SvmSetResp),
                                 {| ps_is_valid := false;
                                    ps_value := ps_value st;
                                    ps_request_from := ps_request_from st |})
                      else Some ((theOtherChild efrom, SvmInvReq) :: nil, None,
                                 {| ps_is_valid := ps_is_valid st;
                                    ps_value := ps_value st;
                                    ps_request_from := Some (efrom, false) |})
            end
        | _ => fun _ => None
        end.

    Definition ParentInvResp : RuleT SingleValueMsg ParentState :=
      fun imsg =>
        match imsg with
        | (efrom, SvmInvResp v) =>
          fun st =>
            match ps_request_from st with
            | None => None
            | Some (childTo, is_get) =>
              Some ((childTo, if is_get then SvmGetResp v else SvmSetResp) :: nil,
                    None,
                    {| ps_is_valid := ps_is_valid st;
                       ps_value := ps_value st;
                       ps_request_from := None |})
            end
        | _ => fun _ => None
        end.

    Definition parent : Object SingleValueMsg ParentState :=
      {| obj_idx := 0;
         obj_state_init := {| ps_is_valid := true;
                              ps_value := 0;
                              ps_request_from := None |};
         obj_rules := ParentGetReq :: ParentSetReq :: ParentInvResp :: nil |}.

  End Parent.

  Section Child.

    (* from external *)
    Definition ChildGetReq : RuleT SingleValueMsg ChildState :=
      fun imsg =>
        match imsg with
        | (efrom, SvmGetReq) =>
          fun st =>
            match cs_request_from st with
            | Some _ => None
            | None =>
              if cs_is_valid st
              then Some (nil, Some (efrom, SvmGetResp (cs_value st)), st)
              else Some ((parentIdx, SvmGetReq) :: nil,
                         None,
                         {| cs_is_valid := cs_is_valid st;
                            cs_value := cs_value st;
                            cs_request_from := Some (efrom, O) |})
            end
        | _ => fun _ => None
        end.

    (* from the parent *)
    Definition ChildGetResp : RuleT SingleValueMsg ChildState :=
      fun imsg =>
        match imsg with
        | (parentIdx, SvmGetResp v) =>
          fun st =>
            match cs_request_from st with
            | None => None
            | Some (efrom, _) =>
              Some (nil, Some (efrom, SvmGetResp v), {| cs_is_valid := true;
                                                        cs_value := v;
                                                        cs_request_from := None |})
            end
        | _ => fun _ => None
        end.

    (* from external *)
    Definition ChildSetReq : RuleT SingleValueMsg ChildState :=
      fun imsg =>
        match imsg with
        | (efrom, SvmSetReq v) =>
          fun st =>
            match cs_request_from st with
            | Some _ => None
            | None =>
              if cs_is_valid st
              then Some (nil, Some (efrom, SvmSetResp),
                         {| cs_is_valid := cs_is_valid st;
                            cs_value := v;
                            cs_request_from := cs_request_from st |})
              else Some ((parentIdx, SvmSetReq v) :: nil,
                         None,
                         {| cs_is_valid := cs_is_valid st;
                            cs_value := cs_value st;
                            cs_request_from := Some (efrom, v) |})
            end
        | _ => fun _ => None
        end.

    (* from the parent *)
    Definition ChildSetResp : RuleT SingleValueMsg ChildState :=
      fun imsg =>
        match imsg with
        | (parentIdx, SvmSetResp) =>
          fun st =>
            match cs_request_from st with
            | None => None
            | Some (efrom, v) =>
              Some (nil, Some (efrom, SvmSetResp), {| cs_is_valid := true;
                                                      cs_value := v;
                                                      cs_request_from := None |})
            end
        | _ => fun _ => None
        end.

    (* from the parent *)
    Definition ChildInvReq : RuleT SingleValueMsg ChildState :=
      fun imsg =>
        match imsg with
        | (parentIdx, SvmInvReq) =>
          fun st =>
            match cs_request_from st with
            | Some _ => None
            | None => Some ((parentIdx, SvmInvResp (cs_value st)) :: nil,
                            None, {| cs_is_valid := false;
                                     cs_value := cs_value st;
                                     cs_request_from := cs_request_from st |})
            end
        | _ => fun _ => None
        end.

    Definition child1 : Object SingleValueMsg ChildState :=
      {| obj_idx := 1;
         obj_state_init := {| cs_is_valid := false;
                              cs_value := 0;
                              cs_request_from := None |};
         obj_rules := ChildGetReq :: ChildGetResp :: ChildSetReq :: ChildSetResp
                                  :: ChildInvReq :: nil |}.

    Definition child2 : Object SingleValueMsg ChildState :=
      {| obj_idx := 2;
         obj_state_init := {| cs_is_valid := false;
                              cs_value := 0;
                              cs_request_from := None |};
         obj_rules := ChildGetReq :: ChildGetResp :: ChildSetReq :: ChildSetResp
                                  :: ChildInvReq :: nil |}.

  End Child.

  Definition impl : Objects SingleValueMsg :=
    (existT (fun st => Object SingleValueMsg st) _ parent)
      :: (existT (fun st => Object SingleValueMsg st) _ child1)
      :: (existT (fun st => Object SingleValueMsg st) _ child2)
      :: nil.

End Impl.

