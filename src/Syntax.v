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

  Inductive RqRs := Rq | Rs.

  Record Msg :=
    { msg_id: IdxT;
      msg_rr: RqRs;
      msg_value: Value
    }.

  Definition buildMsg mid rr v :=
    {| msg_id := mid;
       msg_rr := rr;
       msg_value := v |}.

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
    - decide equality.
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
 * an object is handling now.
 *)

Record RqInfo (MsgT: Type) :=
  { rqh_msg: MsgT;
    rqh_from: IdxT;
    rqh_fwds: list IdxT
  }.

Definition buildRqInfo {MsgT} (rq: Id MsgT) (fwds: list IdxT) :=
  {| rqh_msg := valOf rq;
     rqh_from := idOf rq;
     rqh_fwds := fwds |}.

Definition ORq (MsgT: Type) := list (RqInfo MsgT).
Definition ORqs (MsgT: Type) := M.t (ORq MsgT).

Definition addRq {MsgT} (orq: ORq MsgT) (rq: Id MsgT) (fwds: list IdxT): ORq MsgT :=
  (buildRqInfo rq fwds) :: orq.

Fixpoint getRq {MsgT} (orq: ORq MsgT) (idx: IdxT) :=
  match orq with
  | nil => None
  | rq :: orq' =>
    if rqh_from rq ==n idx then Some rq else getRq orq' idx
  end.

Fixpoint removeRq {MsgT} (orq: ORq MsgT) (ridx: IdxT) :=
  match orq with
  | nil => nil
  | rq :: orq' =>
    if rqh_from rq ==n ridx then orq' else rq :: removeRq orq' ridx
  end.

Definition orqMap {MsgT1 MsgT2: Type} (f: MsgT1 -> MsgT2) (orq: ORq MsgT1) :=
  map (fun ri => {| rqh_msg := f (rqh_msg ri);
                    rqh_from := rqh_from ri;
                    rqh_fwds := rqh_fwds ri |}) orq.

Section Rule.

  Definition OPrec :=
    OState -> ORq Msg -> list (Id Msg) -> Prop.
  Definition OTrs :=
    OState -> ORq Msg -> list (Id Msg) -> (OState * ORq Msg * list (Id Msg)).

  Definition OPrecAnd (p1 p2: OPrec): OPrec :=
    fun ost orq ins => p1 ost orq ins /\ p2 ost orq ins.

  Definition OPrecImp (p1 p2: OPrec): Prop :=
    forall ost orq ins, p1 ost orq ins -> p2 ost orq ins.

  Record Rule :=
    { rule_oidx: IdxT;
      rule_msg_ids: list IdxT;
      rule_minds: list IdxT;
      rule_precond: OPrec;
      rule_trs: OTrs;
    }.

End Rule.

Infix "/\oprec" := OPrecAnd (at level 80).
Infix "->oprec" := OPrecImp (at level 99).
Notation "'⊤oprec'" := (fun _ _ _ => True).
Notation "'⊥oprec'" := (fun _ _ _ => False).
Notation "'=otrs'" := (fun post porq pmsgs => (post, porq, pmsgs)).

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

