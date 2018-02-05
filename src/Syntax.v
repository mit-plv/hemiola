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

  Definition msg_dec: forall m1 m2: Msg, {m1 = m2} + {m1 <> m2}.
  Proof.
    decide equality.
    - apply value_dec.
    - apply msgId_dec.
  Defined.

End Msg.

Section Rule.

  Definition StateT := M.t Value.

  Record TrsHelperUnit :=
    { tst_rqval: Value;
      tst_rss: list (IdxT * option Value)
    }.
  Definition TrsHelper := M.t (* transaction index *) TrsHelperUnit.
  Definition trsHelperInit: TrsHelper := M.empty _.

  Record OState :=
    { ost_st: StateT;
      ost_tst: TrsHelper
    }.

  Definition RPrecond := OState -> Value (* input *) -> Prop.
  Definition RPostcond :=
    OState (* prestate *) -> Value (* input value *) ->
    OState (* poststate *) -> list Msg (* output messages *) -> Prop.

  Record Rule :=
    { rule_mid: MsgId;
      rule_precond: RPrecond;
      rule_postcond: RPostcond;
    }.

End Rule.

Section Conditions.

  Definition Precond := OState -> Value (* input *) -> Prop.
  Definition Postcond := OState -> list Msg -> Prop.

  Definition impRPost (rpostc: RPostcond) (postc: Postcond) :=
    forall pre val post outs,
      rpostc pre val post outs -> postc post outs.

  Definition MsgOuts :=
    OState (* prestate *) -> Value (* input value *) -> list Msg.
  Definition PostcondSt :=
    OState (* prestate *) -> Value (* input value *) -> OState (* poststate *) -> Prop.

  Definition rpostOf (pst: PostcondSt) (mouts: MsgOuts): RPostcond :=
    fun pre val post outs =>
      pst pre val post /\ outs = mouts pre val.

  Definition impPre (pre1 pre2: Precond) :=
    forall pre val, pre1 pre val -> pre2 pre val.

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

Infix "-->" := impPre (at level 30).
Infix "==>" := impPost (at level 30).
Infix "~~>" := impRPost (at level 30).

Hint Resolve impPre_refl impPre_trans impPost_refl impPost_trans.

Record Object :=
  { obj_idx: nat;
    obj_state_init: StateT;
    obj_rules: list Rule;
  }.

Definition System := list Object.

Definition indicesOf (sys: System) :=
  map (fun o => obj_idx o) sys.
Definition initsOf (sys: System) :=
  map (fun o => obj_state_init o) sys.
Definition iisOf (sys: System) :=
  map (fun o => (obj_idx o, obj_state_init o)) sys.
Definition rulesOf (sys: System): list Rule :=
  concat (map (fun o => obj_rules o) sys).

Definition objOf (sys: System) (oidx: IdxT): option Object :=
  find (fun o => if obj_idx o ==n oidx then true else false) sys.
Definition objRulesOf (sys: System) (oidx: IdxT) :=
  (objOf sys oidx) >>=[nil] (fun obj => obj_rules obj).

Fixpoint getForwards (topo: list MsgAddr) (oidx: IdxT) :=
  map ma_to (filter (fun c => if ma_from c ==n oidx then true else false) topo).

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

Lemma iisOf_initsOf:
  forall sys1 sys2,
    iisOf sys1 = iisOf sys2 -> initsOf sys1 = initsOf sys2.
Proof.
  unfold iisOf, initsOf; intros.
  generalize dependent sys2.
  induction sys1 as [|obj1 sys1]; simpl; intros.
  - apply eq_sym, map_eq_nil in H.
    subst; reflexivity.
  - destruct sys2 as [|obj2 sys2]; [discriminate|].
    simpl in H; inv H.
    simpl; erewrite IHsys1 by eassumption.
    rewrite H2; reflexivity.
Qed.

Lemma iisOf_indicesOf:
  forall sys1 sys2,
    iisOf sys1 = iisOf sys2 -> indicesOf sys1 = indicesOf sys2.
Proof.
  unfold iisOf, indicesOf; intros.
  generalize dependent sys2.
  induction sys1 as [|obj1 sys1]; simpl; intros.
  - apply eq_sym, map_eq_nil in H.
    subst; reflexivity.
  - destruct sys2 as [|obj2 sys2]; [discriminate|].
    simpl in H; inv H.
    simpl; erewrite IHsys1 by eassumption.
    rewrite H1; reflexivity.
Qed.
  
Definition singleton (obj: Object): System := obj :: nil.

Definition isExternal (sys: System) (idx: IdxT) :=
  if idx ?<n (indicesOf sys) then false else true.
Definition isInternal (sys: System) (idx: IdxT) :=
  if idx ?<n (indicesOf sys) then true else false.

Notation "'⊤'" := (fun _ _ => True).
Notation "'⊤⊤'" := (fun _ _ _ => True).
Notation "'⊤⊤='" := (fun pre v post => pre = post).
Notation "[ obj ]" := (singleton obj).

