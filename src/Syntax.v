Require Import Bool Vector List String Peano_dec DecidableClass.
Require Import Common FMap HVector.

Set Implicit Arguments.

Local Open Scope string.
Local Open Scope list.
Local Open Scope fmap.

(* Design protocols for a single line first *)
Definition AddrT := unit.

Class DecValue :=
  { t_type: Type;
    t_default: t_type;
    t_eq_dec: forall t1 t2: t_type, {t1 = t2} + {t1 <> t2}
  }.
Global Coercion t_type: DecValue >-> Sortclass.

Section Msg.
  Context `{Value: DecValue}.

  Record Msg :=
    { msg_id: IdxT;
      msg_type: bool;
      msg_addr: AddrT;
      msg_value: Value;
    }.

  Definition MRq: bool := false.
  Definition MRs: bool := true.

  Definition msg_dec: forall m1 m2: Msg, {m1 = m2} + {m1 <> m2}.
  Proof.
    decide equality.
    - apply t_eq_dec.
    - decide equality.
    - apply bool_dec.
    - apply idx_dec.
  Defined.

  Definition MSig := (IdxT * (bool * IdxT))%type.

  Definition sig_dec: forall sig1 sig2: MSig, {sig1 = sig2} + {sig1 <> sig2}.
  Proof.
    decide equality.
    - decide equality.
      + apply idx_dec.
      + apply bool_dec.
    - apply idx_dec.
  Defined.

  Definition sigs_dec := list_eq_dec sig_dec.

  Definition sigOf (idm: Id Msg): MSig :=
    (idOf idm, (msg_type (valOf idm), msg_id (valOf idm))).
  Definition sigsOf (msgs: list (Id Msg)): list MSig :=
    List.map sigOf msgs.

  Lemma sigsOf_app:
    forall sigs1 sigs2,
      sigsOf (sigs1 ++ sigs2) = sigsOf sigs1 ++ sigsOf sigs2.
  Proof.
    unfold sigsOf; intros.
    apply map_app.
  Qed.

End Msg.

Class HasInit (SysT StateT: Type) :=
  { initsOf: SysT -> StateT }.

Class OStateIfc :=
  { ost_sz: nat;
    ost_ty: Vector.t Type ost_sz
  }.

Definition OState `{OStateIfc} :=
  hvec ost_ty.

Definition OStates `{OStateIfc} := M.t OState.

Section ORqs.

  (* A request holder [ORq] holds all requests that an object is handling now.
   * This is both for continuing a transaction when getting a corresponding
   * response and providing a proper locking mechanism.
   *)
  Record RqInfo (MsgT: Type) :=
    { rqi_msg: option MsgT;
      rqi_rss: list (IdxT * option MsgT);
      rqi_midx_rsb: option IdxT
    }.

  (* RqType |-> RqInfo *)
  Definition ORq (MsgT: Type) := M.t (RqInfo MsgT).

  (* Object IdxT |-> ORq *)
  Definition ORqs (MsgT: Type) := M.t (ORq MsgT).

  Definition addRq {MsgT} (orq: ORq MsgT) (rqty: IdxT)
             (msg: MsgT) (mrss: list IdxT) (mrsb: IdxT): ORq MsgT :=
    orq+[rqty <- {| rqi_msg := Some msg;
                    rqi_rss := map (fun rs => (rs, None)) mrss;
                    rqi_midx_rsb := Some mrsb |}].

  Definition addRqS {MsgT} (orq: ORq MsgT) (rqty: IdxT)
             (mrss: list IdxT): ORq MsgT :=
    orq+[rqty <- {| rqi_msg := None;
                    rqi_rss := map (fun rs => (rs, None)) mrss;
                    rqi_midx_rsb := None |}].

  Definition getRq {MsgT} (orq: ORq MsgT) (rqty: IdxT): option (RqInfo MsgT) :=
    orq@[rqty] >>=[None] (fun rqinfo => Some rqinfo).

  Definition removeRq {MsgT} (orq: ORq MsgT) (rqty: IdxT): ORq MsgT :=
    M.remove rqty orq.

End ORqs.

Section Rule.
  Context `{DecValue} `{OStateIfc}.

  Definition OPrec :=
    OState -> ORq Msg -> list (Id Msg) -> Prop.
  Definition OTrs :=
    OState -> ORq Msg -> list (Id Msg) ->
    (OState * ORq Msg * list (Id Msg)).

  Definition OPrecAnd (p1 p2: OPrec): OPrec :=
    fun ost orq ins => p1 ost orq ins /\ p2 ost orq ins.

  Definition OPrecImp (p1 p2: OPrec): Prop :=
    forall ost orq ins, p1 ost orq ins -> p2 ost orq ins.

  Record Rule :=
    { rule_idx: IdxT;
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

Record Object `{DecValue} `{OStateIfc} :=
  { obj_idx: IdxT;
    obj_rules: list Rule;
    obj_rules_valid: NoDup (List.map rule_idx obj_rules)
  }.

Lemma rule_same_id_in_object_same:
  forall `{DecValue} `{OStateIfc} (obj: Object) (rule1 rule2: Rule),
    List.In rule1 (obj_rules obj) ->
    List.In rule2 (obj_rules obj) ->
    rule_idx rule1 = rule_idx rule2 ->
    rule1 = rule2.
Proof.
  intros.
  eapply NoDup_map_In; eauto.
  exact (obj_rules_valid obj).
Qed.

Record System `{DecValue} `{OStateIfc} :=
  { sys_objs: list Object;
    sys_oinds_valid: NoDup (List.map obj_idx sys_objs);
    sys_minds: list IdxT;
    sys_merqs: list IdxT;
    sys_merss: list IdxT;
    sys_msg_inds_valid: NoDup (sys_minds ++ sys_merqs ++ sys_merss);
    sys_oss_inits: OStates;
    sys_orqs_inits: ORqs Msg
  }.

Lemma obj_same_id_in_system_same:
  forall `{DecValue} `{OStateIfc} (sys: System) (obj1 obj2: Object),
    List.In obj1 (sys_objs sys) ->
    List.In obj2 (sys_objs sys) ->
    obj_idx obj1 = obj_idx obj2 ->
    obj1 = obj2.
Proof.
  intros.
  eapply NoDup_map_In; eauto.
  exact (sys_oinds_valid sys).
Qed.

Ltac inds_valid_tac :=
  compute;
  repeat (constructor; [intro Hx; dest_in; discriminate|]);
  constructor.

Global Instance System_OStates_HasInit `{DecValue} `{OStateIfc}
  : HasInit System OStates :=
  {| initsOf := sys_oss_inits |}.

Global Instance System_ORqs_HasInit `{DecValue} `{OStateIfc}
  : HasInit System (ORqs Msg) :=
  {| initsOf := sys_orqs_inits |}.
