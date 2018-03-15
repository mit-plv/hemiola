Require Import Bool List String Peano_dec.
Require Import Common FMap.

Set Implicit Arguments.

Open Scope string.
Open Scope list.
Open Scope fmap.

Section Msg.

  Definition IdxT := nat.

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

Definition OState := M.t Value.
Definition OStates := M.t OState.

Section Rule.

  Definition RPrecond := OState -> list Msg (* input messages *) -> Prop.
  Definition RPostcond :=
    OState (* prestate *) -> list Msg (* input messages *) ->
    OState (* poststate *) -> list Msg (* output messages *) -> Prop.

  Record Rule :=
    { rule_mids: list MsgId;
      rule_precond: RPrecond;
      rule_postcond: RPostcond;
    }.

End Rule.

Section Conditions.

  Definition Precond := OState -> list Msg -> Prop.
  Definition Postcond := OState -> list Msg -> Prop.

  Definition impRPost (rpostc: RPostcond) (postc: Postcond) :=
    forall pre val post outs,
      rpostc pre val post outs -> postc post outs.

  Definition MsgOuts :=
    OState (* prestate *) -> list Msg (* input messages *) -> list Msg.
  Definition PostcondSt :=
    OState (* prestate *) -> list Msg (* input messages *) -> OState (* poststate *) -> Prop.

  Definition rpostOf (pst: PostcondSt) (mouts: MsgOuts): RPostcond :=
    fun pre ins post outs =>
      pst pre ins post /\ outs = mouts pre ins.

  Definition impPre (pre1 pre2: Precond) :=
    forall pre ins, pre1 pre ins -> pre2 pre ins.

  Definition impPost (post1 post2: Postcond) :=
    forall post outs, post1 post outs -> post2 post outs.

  Fact impPre_refl: forall pre, impPre pre pre.
  Proof. unfold impPre; auto. Qed.

  Fact impPre_trans:
    forall pre1 pre2 pre3, impPre pre1 pre2 -> impPre pre2 pre3 -> impPre pre1 pre3.
  Proof. unfold impPre; auto. Qed.

  Fact impPost_refl: forall post, impPost post post.
  Proof. unfold impPost; auto. Qed.

  Fact impPost_trans:
    forall post1 post2 post3, impPost post1 post2 -> impPost post2 post3 -> impPost post1 post3.
  Proof. unfold impPost; auto. Qed.

End Conditions.

Section System.

  Class IsSystem (SysT: Type) (StateT: Type) :=
    { indicesOf: SysT -> list IdxT;
      initsOf: SysT -> StateT }.

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

  Global Instance System_OStates_IsSystem : IsSystem System OStates :=
    {| indicesOf := sys_inds;
       initsOf := sys_inits |}.

  Definition rulesOf := sys_rules.

End System.

Section RuleAdder.
  Context {SysT: Type} `{IsSystem SysT OStates}.

  Definition buildRawSys (osys: SysT): System :=
    {| sys_inds := indicesOf osys;
       sys_inits := initsOf osys;
       sys_rules := nil |}.

  Definition addRules (rules: list Rule) (sys: System) :=
    {| sys_inds := sys_inds sys;
       sys_inits := sys_inits sys;
       sys_rules := sys_rules sys ++ rules |}.

End RuleAdder.

