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

Section Rule.
  Variable OState: Type.

  Definition RPrecond := OState -> list Msg (* input messages *) -> Prop.
  Definition RPostcond :=
    OState (* prestate *) -> list Msg (* input messages *) ->
    OState (* poststate *) -> list Msg (* output messages *) -> Prop.

  Record Rule :=
    { rule_mids: list MsgId;
      rule_precond: RPrecond;
      rule_postcond: RPostcond;
    }.

  Definition ValidMsgsIn (oidx: IdxT) {MsgT} `{HasMsg MsgT}
             (msgs: list MsgT) :=
    Forall (fun msg => mid_to (msg_id (getMsg msg)) = oidx) msgs.

End Rule.

Section Conditions.
  Variable OState: Type.

  Definition Precond := OState -> list Msg -> Prop.
  Definition Postcond := OState -> list Msg -> Prop.

  Definition impRPost (rpostc: RPostcond OState) (postc: Postcond) :=
    forall pre val post outs,
      rpostc pre val post outs -> postc post outs.

  Definition MsgOuts :=
    OState (* prestate *) -> list Msg (* input messages *) -> list Msg.
  Definition PostcondSt :=
    OState (* prestate *) -> list Msg (* input messages *) -> OState (* poststate *) -> Prop.

  Definition rpostOf (pst: PostcondSt) (mouts: MsgOuts): RPostcond OState :=
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

Section Object.
  Variable OState: Type.

  Record Object :=
    { obj_idx: IdxT;
      obj_state_init: OState;
      obj_rules: list (Rule OState)
    }.

  Class IsObject (ObjT: Type) :=
    { getIndex : ObjT -> IdxT;
      getOStateInit : ObjT -> OState }.

  Global Instance Object_IsObject : IsObject Object :=
    {| getIndex := obj_idx;
       getOStateInit := obj_state_init |}.

  Class HasObjects (ObjT: Type) `{IsObject ObjT} (SysT: Type) :=
    { getObjects : SysT -> list ObjT }.

End Object.

Definition indicesOf {OState ObjT SysT} `{HasObjects OState ObjT SysT} (sys: SysT) :=
  map (fun o => getIndex o) (getObjects sys).
Definition initsOf {OState ObjT SysT} `{HasObjects OState ObjT SysT} (sys: SysT) :=
  map (fun o => getOStateInit o) (getObjects sys).
Definition objOf {OState ObjT} `{IsObject OState ObjT}
           (sys: list ObjT) (oidx: IdxT): option ObjT :=
  find (fun o => if getIndex o ==n oidx then true else false) sys.

Definition isExternal {OState ObjT SysT} `{HasObjects OState ObjT SysT}
           (sys: SysT) (idx: IdxT) :=
  if idx ?<n (indicesOf sys) then false else true.
Definition isInternal {OState ObjT SysT} `{HasObjects OState ObjT SysT}
           (sys: SysT) (idx: IdxT) :=
  if idx ?<n (indicesOf sys) then true else false.

Section System.
  Variable OState: Type.

  Definition System := list (Object OState).

  Global Instance System_HasObjects : HasObjects System :=
    {| getObjects := id |}.

  Definition rulesOf (sys: System): list (Rule OState) :=
    concat (map (fun o => obj_rules o) sys).

  Definition objRulesOf (sys: System) (oidx: IdxT) :=
    (objOf sys oidx) >>=[nil] (fun obj => obj_rules obj).

  Lemma rulesOf_in:
    forall obj sys,
      In obj sys ->
      forall rule,
        In rule (obj_rules obj) ->
        In rule (rulesOf sys).
  Proof.
    unfold rulesOf; intros.
    induction sys; simpl; intros; [inv H|].
    apply in_or_app.
    inv H; auto.
  Qed.
  
  Definition singleton (obj: Object OState): System := obj :: nil.

End System.

