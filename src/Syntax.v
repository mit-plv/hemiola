Require Import Bool Vector List String Peano_dec.
Require Import Common FMap IList.

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

Fixpoint ostateInds (sz: nat): Vector.t nat sz :=
  match sz with
  | O => Vector.nil _
  | S n => Vector.cons _ n _ (ostateInds n)
  end.

Record OStateIfc :=
  { ost_sz: nat;
    ost_ty: nat -> Type
  }.

Definition OState (ifc: OStateIfc) :=
  @ilist _ (ost_ty ifc) (ost_sz ifc) (ostateInds (ost_sz ifc)).

Record OStateR :=
  { ost_ifc: OStateIfc;
    ost_st: OState ost_ifc
  }.

Definition OStates := M.t OStateR.

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
  Variables (ifc: OStateIfc).

  Definition OPrec :=
    OState ifc -> ORq Msg -> list (Id Msg) -> Prop.
  Definition OTrs :=
    OState ifc -> ORq Msg -> list (Id Msg) ->
    (OState ifc * ORq Msg * list (Id Msg)).

  Definition OPrecAnd (p1 p2: OPrec): OPrec :=
    fun ost orq ins => p1 ost orq ins /\ p2 ost orq ins.

  Definition OPrecImp (p1 p2: OPrec): Prop :=
    forall ost orq ins, p1 ost orq ins -> p2 ost orq ins.

  Record Rule :=
    { rule_idx: IdxT;
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

Record Object :=
  { obj_idx: IdxT;
    obj_ifc: OStateIfc;
    obj_rules: list (Rule obj_ifc);
    obj_rules_valid: NoDup (map (@rule_idx _) obj_rules)
  }.

Record System :=
  { sys_objs: list Object;
    sys_oinds_valid: NoDup (map obj_idx sys_objs);
    sys_minds: list IdxT;
    sys_merqs: list IdxT;
    sys_merss: list IdxT;
    sys_msg_inds_valid: NoDup (sys_minds ++ sys_merqs ++ sys_merss);
    sys_oss_inits: OStates;
    sys_orqs_inits: ORqs Msg
  }.

Global Instance System_OStates_HasInit : HasInit System OStates :=
  {| initsOf := sys_oss_inits |}.

Global Instance System_ORqs_Msg_HasInit : HasInit System (ORqs Msg) :=
  {| initsOf := sys_orqs_inits |}.

