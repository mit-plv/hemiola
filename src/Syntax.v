Require Import Bool Vector List String Peano_dec.
Require Import Common FMap HVector.

Set Implicit Arguments.

Open Scope string.
Open Scope list.
Open Scope fmap.

Definition AddrT := nat.

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
    {| msg_id := mid;
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
    - apply eq_nat_dec.
  Defined.

  Class HasMsg (MsgT: Type) :=
    { getMsg : MsgT -> Msg }.

  Global Instance Msg_HasMsg : HasMsg Msg :=
    { getMsg := id }.

End Msg.

Class HasInit (SysT StateT: Type) :=
  { initsOf: SysT -> StateT }.

Record OStateIfc :=
  { ost_sz: nat;
    ost_ty: Vector.t Type ost_sz
  }.

Definition OState (ifc: OStateIfc) :=
  hvec (ost_ty ifc).

Record OStateR :=
  { ost_ifc: OStateIfc;
    ost_st: OState ost_ifc
  }.

Definition OStates := M.t OStateR.

Section ORqs.

  (* A request holder [ORq] holds all requests that an object is handling now.
   * This is both for continuing a transaction when getting a corresponding
   * response and providing a proper locking mechanism.
   *)
  Record RqInfo (MsgT: Type) :=
    { rqi_msg: MsgT;
      rqi_minds_rss: list IdxT;
      rqi_midx_rsb: IdxT
    }.

  (* AddrT |-> RqType |-> RqInfo *)
  Definition ORq (MsgT: Type) := M.t (M.t (RqInfo MsgT)).

  (* Object IdxT |-> ORq *)
  Definition ORqs (MsgT: Type) := M.t (ORq MsgT). 

  Definition addRq {MsgT} (orq: ORq MsgT) (addr: AddrT) (rqty: IdxT)
             (msg: MsgT) (mrss: list IdxT) (mrsb: IdxT): ORq MsgT :=
    let aorq := match orq@[addr] with
                | Some aorq => aorq
                | None => M.empty _
                end in
    orq+[addr <- aorq+[rqty <- {| rqi_msg := msg;
                                  rqi_minds_rss := mrss;
                                  rqi_midx_rsb := mrsb
                               |}]].

  Fixpoint getRq {MsgT} (orq: ORq MsgT) (addr: AddrT) (rqty: IdxT): option (RqInfo MsgT) :=
    orq@[addr] >>=[None]
       (fun aorq => aorq@[rqty] >>=[None] (fun rqinfo => Some rqinfo)).

  Fixpoint removeRq {MsgT} (orq: ORq MsgT) (addr: AddrT) (rqty: IdxT): ORq MsgT :=
    orq@[addr] >>=[orq]
       (fun aorq => orq +[addr <- (M.remove rqty aorq)]).

  Definition orqMap {MsgT1 MsgT2: Type} (f: MsgT1 -> MsgT2) (orq: ORq MsgT1): ORq MsgT2 :=
    M.map (fun aorq =>
             M.map (fun rqi =>
                      {| rqi_msg := f (rqi_msg rqi);
                         rqi_minds_rss := rqi_minds_rss rqi;
                         rqi_midx_rsb := rqi_midx_rsb rqi
                      |}) aorq)
          orq.

End ORqs.

Section Rule.
  Variables (ifc: OStateIfc).

  Definition OMsgsFrom :=
    ORq Msg -> list IdxT.
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
      rule_msgs_from: OMsgsFrom;
      rule_precond: OPrec;
      rule_trs: OTrs;
    }.

End Rule.

Infix "/\oprec" := OPrecAnd (at level 80).
Infix "->oprec" := OPrecImp (at level 99).
Notation "'⊤oprec'" := (fun _ _ _ => True).
Notation "'⊥oprec'" := (fun _ _ _ => False).
Notation "'=otrs'" := (fun post porq pmsgs => (post, porq, pmsgs)).

Definition broadcaster {MsgT} (minds: list IdxT) (msg: MsgT): list (Id MsgT) :=
  List.map (fun midx => (midx, msg)) minds.

Record Object :=
  { obj_idx: IdxT;
    obj_ifc: OStateIfc;
    obj_rules: list (Rule obj_ifc);
    obj_rules_valid: NoDup (map (@rule_idx _) obj_rules)
  }.

Lemma rules_same_id_in_object_same:
  forall obj (rule1 rule2: Rule (obj_ifc obj)),
    In rule1 (obj_rules obj) ->
    In rule2 (obj_rules obj) ->
    rule_idx rule1 = rule_idx rule2 ->
    rule1 = rule2.
Proof.
  intros.
  eapply NoDup_map_In; eauto.
  exact (obj_rules_valid obj).
Qed.

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

Lemma obj_same_id_in_system_same:
  forall sys (obj1 obj2: Object),
    In obj1 (sys_objs sys) ->
    In obj2 (sys_objs sys) ->
    obj_idx obj1 = obj_idx obj2 ->
    obj1 = obj2.
Proof.
  intros.
  eapply NoDup_map_In; eauto.
  exact (sys_oinds_valid sys).
Qed.

Ltac inds_valid_tac :=
  abstract (compute; repeat (constructor; firstorder)).

Global Instance System_OStates_HasInit : HasInit System OStates :=
  {| initsOf := sys_oss_inits |}.

Global Instance System_ORqs_Msg_HasInit : HasInit System (ORqs Msg) :=
  {| initsOf := sys_orqs_inits |}.

Close Scope string.
Close Scope list.
Close Scope fmap.

