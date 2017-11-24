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
      tst_rqval: Value;
      tst_rss: list (IdxT * option Value)
    }.
  Definition TrsHelper := M.t (* transaction index *) TrsHelperUnit.
  Definition trsHelperInit: TrsHelper := M.empty _.

  Record OState :=
    { ost_st: StateT;
      ost_tst: TrsHelper
    }.

  Definition Cond := OState -> Prop.
  Definition PreCond := Cond.
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

Definition indicesOf (sys: System) :=
  map (fun o => obj_idx o) (sys_objs sys).
Definition initsOf (sys: System) :=
  map (fun o => obj_state_init o) (sys_objs sys).
Definition iisOf (sys: System) :=
  map (fun o => (obj_idx o, obj_state_init o)) (sys_objs sys).
Definition pmsgsOf (sys: System): list PMsg :=
  concat (map (fun o => obj_trs o) (sys_objs sys)).

Definition objOf (sys: System) (oidx: IdxT): option Object :=
  find (fun o => if obj_idx o ==n oidx then true else false) (sys_objs sys).
Definition objPMsgsOf (sys: System) (oidx: IdxT) :=
  (objOf sys oidx) >>=[nil] (fun obj => obj_trs obj).

Fixpoint getForwards (topo: list Channel) (oidx: IdxT) :=
  map chn_to (filter (fun c => if chn_from c ==n oidx then true else false) topo).

Lemma pmsgsOf_in:
  forall obj sys,
    In obj (sys_objs sys) ->
    forall pmsg,
      In pmsg (obj_trs obj) ->
      In pmsg (pmsgsOf sys).
Proof.
  unfold pmsgsOf; intros.
  remember (sys_objs sys) as obs; clear Heqobs sys.
  induction obs; simpl; intros; [inv H|].
  apply in_or_app.
  inv H; auto.
Qed.

Lemma iisOf_initsOf:
  forall sys1 sys2,
    iisOf sys1 = iisOf sys2 -> initsOf sys1 = initsOf sys2.
Proof.
  unfold iisOf, initsOf; intros.
  remember (sys_objs sys1) as obs1; clear Heqobs1.
  remember (sys_objs sys2) as obs2; clear Heqobs2.
  clear sys1 sys2.
  generalize dependent obs2.
  induction obs1 as [|obj1 obs1]; simpl; intros.
  - apply eq_sym, map_eq_nil in H.
    subst; reflexivity.
  - destruct obs2 as [|obj2 obs2]; [discriminate|].
    simpl in H; inv H.
    simpl; erewrite IHobs1 by eassumption.
    rewrite H2; reflexivity.
Qed.

Lemma iisOf_indicesOf:
  forall sys1 sys2,
    iisOf sys1 = iisOf sys2 -> indicesOf sys1 = indicesOf sys2.
Proof.
  unfold iisOf, indicesOf; intros.
  remember (sys_objs sys1) as obs1; clear Heqobs1.
  remember (sys_objs sys2) as obs2; clear Heqobs2.
  clear sys1 sys2.
  generalize dependent obs2.
  induction obs1 as [|obj1 obs1]; simpl; intros.
  - apply eq_sym, map_eq_nil in H.
    subst; reflexivity.
  - destruct obs2 as [|obj2 obs2]; [discriminate|].
    simpl in H; inv H.
    simpl; erewrite IHobs1 by eassumption.
    rewrite H1; reflexivity.
Qed.
  
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

