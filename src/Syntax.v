Require Import Bool List String Peano_dec.
Require Import Common FMap.

Set Implicit Arguments.

Open Scope string.
Open Scope list.
Open Scope fmap.

Section Msg.

  Definition IdxT := nat.

  Definition MsgT := string.
  Definition msgT_dec := string_dec.

  (* A message is always either a request or a response. *)
  Inductive RqRs := Rq | Rs.

  Record MsgId :=
    { mid_rq : IdxT; (* an object that requests this message *)
      mid_rs : IdxT; (* an object that responses this message *)
      mid_type : MsgT;
      mid_rqrs : RqRs;
      mid_chn : IdxT (* which channel (queue) to use *)
    }.

  Definition buildMsgId rq rs ty rr cn :=
    {| mid_rq := rq; mid_rs := rs; mid_type := ty; mid_rqrs := rr; mid_chn := cn |}.

  Definition msgId_dec: forall m1 m2: MsgId, {m1 = m2} + {m1 <> m2}.
  Proof. repeat decide equality. Defined.

  Definition isTrsPair (rq rs: MsgId) :=
    (if mid_rq rq ==n mid_rq rs then true else false)
      && (if mid_rs rq ==n mid_rs rs then true else false)
      && (if msgT_dec (mid_type rq) (mid_type rs) then true else false)
      && (match mid_rqrs rq, mid_rqrs rs with
          | Rq, Rs => true
          | _, _ => false
          end).

  Inductive Value :=
  | VUnit
  | VBool (b: bool)
  | VNat (n: nat)
  | VPair (v1 v2: Value).

  Definition value_dec: forall v1 v2: Value, {v1 = v2} + {v1 <> v2}.
  Proof. repeat decide equality. Defined.

  Record Msg :=
    { msg_id: MsgId;
      msg_value: Value
    }.

  Definition msg_dec: forall m1 m2: Msg, {m1 = m2} + {m1 <> m2}.
  Proof. repeat decide equality. Defined.

  Definition msgFrom (msg: MsgId) :=
    match mid_rqrs msg with
    | Rq => mid_rq msg
    | Rs => mid_rs msg
    end.

  Definition msgTo (msg: MsgId) :=
    match mid_rqrs msg with
    | Rq => mid_rs msg
    | Rs => mid_rq msg
    end.

End Msg.

Section PMsg.

  Definition StateT := M.t Value.

  Record PMsg :=
    { pmsg_mid: MsgId;
      pmsg_precond: StateT -> Prop;
      pmsg_outs: StateT -> Value -> list Msg;
      pmsg_postcond: StateT (* prestate *) -> Value -> StateT (* poststate *) -> Prop
    }.

  Definition CondT := StateT -> Prop.
  Definition CondImp (c1 c2: CondT) := forall st, c1 st -> c2 st.
  Definition postOf (pmsg: PMsg): CondT :=
    fun post => forall pre mt, pmsg_postcond pmsg pre mt post.
  Definition Disjoint (c1 c2: CondT) := forall st, c1 st -> c2 st -> False.

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

Notation "'T'" := (fun _ => True).
Infix "-->" := CondImp (at level 30).
Infix "-*-" := Disjoint (at level 30).
Notation "[ obj ]" := (singleton obj).

