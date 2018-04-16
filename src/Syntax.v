Require Import Bool List String Peano_dec.
Require Import Common FMap.

Set Implicit Arguments.

Open Scope string.
Open Scope list.
Open Scope fmap.

Section Msg.

  (* Semantically, there is an 1-1 correspondence between [MsgAddr] and a
   * channel (≈ queue, fifo) in a target system.
   *)
  Record MsgAddr :=
    { ma_from : IdxT; (* an object that requests this message *)
      ma_to : IdxT; (* an object that responses this message *)
      ma_chn : IdxT (* which channel to use *)
    }.

  Definition buildMsgAddr fr to cn :=
    {| ma_from := fr; ma_to := to; ma_chn := cn |}.

  (* NOTE: [mid_tid] is a "transaction" id; all messages representing a certain
   * transaction have the same [mid_tid]. Such messages are still 
   * distinguishable by [mid_addr]. It is generally assumed that each channel is
   * used at most once during the transaction.
   *)
  Record MsgId :=
    { mid_addr : MsgAddr;
      mid_tid : IdxT; (* a transaction id *)
    }.

  Definition mid_from := fun mid => ma_from (mid_addr mid).
  Definition mid_to := fun mid => ma_to (mid_addr mid).
  Definition mid_chn := fun mid => ma_chn (mid_addr mid).  

  Definition buildMsgId tid fr to cn :=
    {| mid_addr := {| ma_from := fr; ma_to := to; ma_chn := cn |};
       mid_tid := tid |}.

  Definition msgAddr_dec: forall m1 m2: MsgAddr, {m1 = m2} + {m1 <> m2}.
  Proof. repeat decide equality. Defined.

  Definition msgId_dec: forall m1 m2: MsgId, {m1 = m2} + {m1 <> m2}.
  Proof.
    decide equality.
    - decide equality.
    - apply msgAddr_dec.
  Defined.

  (* No conditions about [mid_chn]; it's only about liveness. *)
  Definition DualMid (rq rs: MsgId) :=
    mid_tid rq = mid_tid rs /\
    mid_from rq = mid_to rs /\
    mid_to rq = mid_from rs.

  Definition dualOf (mid: MsgId) (dchn: IdxT) :=
    {| mid_addr := {| ma_from := ma_to (mid_addr mid);
                      ma_to := ma_from (mid_addr mid);
                      ma_chn := dchn |};
       mid_tid := mid_tid mid |}.

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

  Definition buildMsg mid v :=
    {| msg_id := mid; msg_value := v |}.

  Fixpoint buildMsgs mids vals :=
    match mids with
    | nil => nil
    | mid :: mids' =>
      match vals with
      | nil => nil
      | val :: vals' => (buildMsg mid val) :: (buildMsgs mids' vals')
      end
    end.

  Definition msg_dec: forall m1 m2: Msg, {m1 = m2} + {m1 <> m2}.
  Proof.
    decide equality.
    - apply value_dec.
    - apply msgId_dec.
  Defined.

  Class HasMsg (MsgT: Type) :=
    { getMsg : MsgT -> Msg }.

  Global Instance Msg_HasMsg : HasMsg Msg :=
    { getMsg := id }.

End Msg.

Class HasInit (SysT StateT: Type) :=
  { initsOf: SysT -> StateT }.

Definition OState := M.t Value.
Definition OStates := M.t OState.

(* A request holder [ORq] holds all requests that 
 * the target object is handling now.
 *)
Definition ORq (MsgT: Type) := list MsgT.
Definition ORqs (MsgT: Type) := M.t (ORq MsgT).

Definition addRq {MsgT} (orq: ORq MsgT) (rq: MsgT): ORq MsgT :=
  rq :: orq.

Fixpoint getRq {MsgT} (idxf: MsgT -> IdxT) (orq: ORq MsgT) (idx: IdxT) :=
  match orq with
  | nil => None
  | rq :: orq' =>
    if idxf rq ==n idx then Some rq else getRq idxf orq' idx
  end.

Fixpoint removeRq {MsgT} (idxf: MsgT -> IdxT) (orq: ORq MsgT) (ridx: IdxT) :=
  match orq with
  | nil => nil
  | rq :: orq' =>
    if idxf rq ==n ridx then orq' else rq :: removeRq idxf orq' ridx
  end.

Section Rule.

  Definition RPrecond := OState -> ORq Msg -> list Msg (* input messages *) -> Prop.
  Definition RPostcond :=
    OState -> ORq Msg (* prestates *) -> list Msg (* input messages *) ->
    OState -> ORq Msg (* poststates *) -> list Msg (* output messages *) -> Prop.

  Record Rule :=
    { rule_mids: list MsgId;
      rule_precond: RPrecond;
      rule_postcond: RPostcond;
    }.

End Rule.

Section Conditions.

  Definition MsgOuts :=
    OState (* prestate *) -> list Msg (* input messages *) -> list Msg.
  Definition PostcondSt :=
    OState (* prestate *) -> list Msg (* input messages *) -> OState (* poststate *) -> Prop.
  Definition PostcondORq :=
    ORq Msg -> list Msg (* input messages *) -> ORq Msg -> Prop.

  Definition rpostOf (pcondSt: PostcondSt) (pcondORq: PostcondORq) (mouts: MsgOuts): RPostcond :=
    fun post porq ins nost norq outs =>
      pcondSt post ins nost /\
      pcondORq porq ins norq /\
      outs = mouts post ins.

End Conditions.

Section System.

  Class IsSystem (SysT: Type) :=
    { indicesOf: SysT -> list IdxT }.

  Global Instance IsSystem_ORqs_HasInit
         {SysT MsgT} `{IsSystem SysT} : HasInit SysT (ORqs MsgT) :=
    {| initsOf := fun sys => M.replicate (indicesOf sys) (@nil _) |}.

  Definition isExternal {SysT} `{IsSystem SysT} (sys: SysT) (idx: IdxT) :=
    if idx ?<n (indicesOf sys) then false else true.
  Definition isInternal {SysT} `{IsSystem SysT} (sys: SysT) (idx: IdxT) :=
    if idx ?<n (indicesOf sys) then true else false.

  Definition fromExternal {SysT MsgT} `{IsSystem SysT} `{HasMsg MsgT}
             (sys: SysT) (msg: MsgT) :=
    isExternal sys (mid_from (msg_id (getMsg msg))).
  Definition fromInternal {SysT MsgT} `{IsSystem SysT} `{HasMsg MsgT}
             (sys: SysT) (msg: MsgT) :=
    isInternal sys (mid_from (msg_id (getMsg msg))).

  Definition toExternal {SysT MsgT} `{IsSystem SysT} `{HasMsg MsgT}
             (sys: SysT) (msg: MsgT) :=
    isExternal sys (mid_to (msg_id (getMsg msg))).
  Definition toInternal {SysT MsgT} `{IsSystem SysT} `{HasMsg MsgT}
             (sys: SysT) (msg: MsgT) :=
    isInternal sys (mid_to (msg_id (getMsg msg))).
  
  Record System :=
    { sys_inds: list IdxT;
      sys_inits: OStates;
      sys_rules: list Rule }.

  Global Instance System_IsSystem : IsSystem System :=
    {| indicesOf := sys_inds |}.

  Global Instance System_OStates_HasInit : HasInit System OStates :=
    {| initsOf := sys_inits |}.

  Definition rulesOf := sys_rules.

  Definition handlersOf (rules: list Rule): list MsgId :=
    concat (map rule_mids rules).

  Definition extHandlersOf (sys: System): list MsgId :=
    filter (fun mid => isExternal sys (mid_from mid))
           (handlersOf (sys_rules sys)).

  Definition ExtHandles (sys: System) (erqs: list MsgId) :=
    extHandlersOf sys = erqs.

End System.

Ltac evalIndicesOf sys :=
  let indices := eval cbn in (sys_inds sys) in exact indices.

Section RuleAdder.
  Context {SysT: Type}
          `{IsSystem SysT} `{HasInit SysT OStates}.

  Definition buildRawSys (osys: SysT): System :=
    {| sys_inds := indicesOf osys;
       sys_inits := initsOf osys;
       sys_rules := nil |}.

  Definition addRules (rules: list Rule) (sys: System) :=
    {| sys_inds := sys_inds sys;
       sys_inits := sys_inits sys;
       sys_rules := sys_rules sys ++ rules |}.

End RuleAdder.

