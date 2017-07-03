Require Import List String Peano_dec.
Require Import Language.

Set Implicit Arguments.

Open Scope list.

Inductive SingleValueMsg :=
| SvmGetReq
| SvmGetResp (v: nat)
| SvmSetReq (v: nat)
| SvmSetResp.

Definition svm_is_req (svm: SingleValueMsg) :=
  match svm with
  | SvmGetReq
  | SvmSetReq _ => true
  | _ => false
  end.

Section Spec.

  Definition SpecState := nat. (* a single value *)

  Definition SpecGetReq : RuleT SingleValueMsg SpecState :=
    fun imsg =>
      match imsg with
      | (from, SvmGetReq) => fun st => Some (nil, (from, SvmGetResp st) :: nil, st)
      | _ => fun _ => None
      end.

  Definition SpecSetReq : RuleT SingleValueMsg SpecState :=
    fun imsg =>
      match imsg with
      | (from, SvmSetReq v) => fun _ => Some (nil, (from, SvmSetResp) :: nil, v)
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

