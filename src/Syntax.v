Require Import Bool List String Peano_dec.
Require Import Common FMap.

Set Implicit Arguments.

Open Scope string.
Open Scope list.
Open Scope fmap.

Section Msg.

  Definition IdxT := nat.

  Record MsgId :=
    { mid_type : IdxT;
      mid_from : IdxT; (* an object that requests this message *)
      mid_to : IdxT; (* an object that responses this message *)
      mid_chn : IdxT (* which channel (queue) to use *)
    }.

  Definition buildMsgId ty fr to cn :=
    {| mid_type := ty; mid_from := fr; mid_to := to; mid_chn := cn |}.

  Definition msgId_dec: forall m1 m2: MsgId, {m1 = m2} + {m1 <> m2}.
  Proof. repeat decide equality. Defined.

  Inductive Value :=
  | VUnit
  | VBool (b: bool)
  | VNat (n: nat)
  | VPair (v1 v2: Value)
  | VList (vl: list Value).

  Fixpoint value_dec (v1 v2: Value): {v1 = v2} + {v1 <> v2}.
  Proof.
    decide equality.
    - repeat decide equality.
    - repeat decide equality.
    - decide equality.
  Defined.

  Record Msg :=
    { msg_id: MsgId;
      msg_value: Value
    }.

  Definition msg_dec: forall m1 m2: Msg, {m1 = m2} + {m1 <> m2}.
  Proof.
    decide equality.
    - apply value_dec.
    - apply msgId_dec.
  Defined.

End Msg.

Section PMsg.

  Definition StateT := M.t Value.

  Record TrsHelperUnit :=
    { tst_rqfrom: IdxT;
      tst_rqfwds: list (IdxT * option Value)
    }.
  Definition TrsHelper := M.t (* transaction index *) TrsHelperUnit.
  Definition trsHelperInit: TrsHelper := M.empty _.

  Record OState :=
    { ost_st: StateT;
      ost_tst: TrsHelper
    }.

  Definition PreCond := OState -> Prop.
  Definition PostCond :=
    OState (* prestate *) -> Value -> OState (* poststate *) -> Prop.
  Definition MsgOuts := OState -> Value -> list Msg.

  Record PMsg :=
    { pmsg_mid: MsgId;
      pmsg_precond: PreCond;
      pmsg_outs: MsgOuts;
      pmsg_postcond: PostCond
    }.

End PMsg.

Record Object :=
  { obj_idx: nat;
    obj_state_init: StateT;
    obj_trs: list PMsg;
  }.

Record Channel :=
  { chn_from: IdxT;
    chn_to: IdxT;
    chn_idx: IdxT (* same [chn_from] and [chn_to], but may require multiple channels *)
  }.

Definition buildChannel from to idx :=
  {| chn_from := from; chn_to := to; chn_idx := idx |}.

Record System :=
  { sys_objs: list Object;
    sys_chns: list Channel
  }.

Definition indicesOf (sys: System) := map (fun o => obj_idx o) (sys_objs sys).
Definition singleton (obj: Object): System :=
  {| sys_objs := obj :: nil;
     sys_chns := nil
  |}.

Definition isExternal (sys: System) (idx: IdxT) :=
  if idx ?<n (indicesOf sys) then false else true.
Definition isInternal (sys: System) (idx: IdxT) :=
  if idx ?<n (indicesOf sys) then true else false.

Notation "'T'" := (fun _ => True).
Notation "[ obj ]" := (singleton obj).

