Require Import Bool List String Peano_dec.
Require Import Common FMap.

Set Implicit Arguments.

Open Scope string.
Open Scope list.
Open Scope fmap.

Section Msg.

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
    { msg_id: IdxT;
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
    - apply eq_nat_dec.
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

  Definition RPrecond := OState -> ORq Msg ->
                         list (Id Msg) (* input messages *) -> Prop.
  Definition RPostcond :=
    OState -> ORq Msg (* prestates *) -> list (Id Msg) (* input messages *) ->
    OState -> ORq Msg (* poststates *) -> list (Id Msg) (* output messages *) -> Prop.

  Definition RPrecAnd (p1 p2: RPrecond): RPrecond :=
    fun ost orq ins => p1 ost orq ins /\ p2 ost orq ins.

  Definition RPrecImp (p1 p2: RPrecond): Prop :=
    forall ost orq ins, p1 ost orq ins -> p2 ost orq ins.

  Definition RPostAnd (p1 p2: RPostcond): RPostcond :=
    fun post porq ins nost norq outs =>
      p1 post porq ins nost norq outs /\ p2 post porq ins nost norq outs.

  Definition RPostImp (p1 p2: RPostcond): Prop :=
    forall post porq ins nost norq outs,
      p1 post porq ins nost norq outs -> p2 post porq ins nost norq outs.

  Record Rule :=
    { rule_oidx: IdxT;
      rule_msg_ids: list IdxT;
      rule_minds: list IdxT;
      rule_precond: RPrecond;
      rule_postcond: RPostcond;
    }.

End Rule.

Infix "/\rprec" := RPrecAnd (at level 80).
Infix "->rprec" := RPrecImp (at level 99).
Infix "/\rpost" := RPostAnd (at level 80).
Infix "->rpost" := RPostImp (at level 99).

Section Conditions.

  Definition MsgOuts :=
    OState (* prestate *) -> list (Id Msg) (* input messages *) ->
    list (Id Msg).
  Definition PostcondSt :=
    OState (* prestate *) -> list (Id Msg) (* input messages *) ->
    OState (* poststate *) -> Prop.
  Definition PostcondORq :=
    ORq Msg -> list (Id Msg) (* input messages *) -> ORq Msg -> Prop.

  Definition rpostOf (pcondSt: PostcondSt)
             (pcondORq: PostcondORq) (mouts: MsgOuts): RPostcond :=
    fun post porq ins nost norq outs =>
      pcondSt post ins nost /\
      pcondORq porq ins norq /\
      outs = mouts post ins.

End Conditions.

Section System.

  Class IsSystem (SysT: Type) :=
    { oindsOf: SysT -> list IdxT;
      mindsOf: SysT -> list IdxT;
      merqsOf: SysT -> list IdxT;
      merssOf: SysT -> list IdxT;
      msg_inds_valid:
        forall sys,
          NoDup (mindsOf sys ++ merqsOf sys ++ merssOf sys)
    }.

  Global Instance IsSystem_ORqs_HasInit
         {SysT MsgT} `{IsSystem SysT} : HasInit SysT (ORqs MsgT) :=
    {| initsOf := fun sys => M.replicate (oindsOf sys) (@nil _) |}.

  Context {SysT MsgT} `{IsSystem SysT} `{HasMsg MsgT}.

  Record System :=
    { sys_oinds: list IdxT;
      sys_minds: list IdxT;
      sys_merqs: list IdxT;
      sys_merss: list IdxT;
      sys_msg_inds_valid: NoDup (sys_minds ++ sys_merqs ++ sys_merss);
      sys_inits: OStates;
      sys_rules: list Rule
    }.

  Global Instance System_IsSystem : IsSystem System :=
    {| oindsOf := sys_oinds;
       mindsOf := sys_minds;
       merqsOf := sys_merqs;
       merssOf := sys_merss;
       msg_inds_valid := sys_msg_inds_valid
    |}.

  Global Instance System_OStates_HasInit : HasInit System OStates :=
    {| initsOf := sys_inits |}.

End System.

Ltac evalOIndsOf sys :=
  let indices := eval cbn in (sys_oinds sys) in exact indices.

Ltac evalMIndsOf sys :=
  let indices := eval cbn in (sys_minds sys) in exact indices.

Section RuleAdder.
  Context {SysT: Type}
          `{IsSystem SysT} `{HasInit SysT OStates}.

  Definition buildRawSys (osys: SysT): System :=
    {| sys_oinds := oindsOf osys;
       sys_minds := mindsOf osys;
       sys_merqs := merqsOf osys;
       sys_merss := merssOf osys;
       sys_msg_inds_valid := msg_inds_valid osys;
       sys_inits := initsOf osys;
       sys_rules := nil |}.

  Definition addRules (rules: list Rule) (sys: System) :=
    {| sys_oinds := sys_oinds sys;
       sys_minds := sys_minds sys;
       sys_merqs := sys_merqs sys;
       sys_merss := sys_merss sys;
       sys_msg_inds_valid := sys_msg_inds_valid sys;
       sys_inits := sys_inits sys;
       sys_rules := sys_rules sys ++ rules |}.

End RuleAdder.

