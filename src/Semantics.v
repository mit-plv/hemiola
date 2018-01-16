Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax.

Set Implicit Arguments.

Section HasMsg.
  Class HasMsg (MsgT: Type) :=
    { getMsg : MsgT -> Msg }.

  Global Instance Msg_HasMsg : HasMsg Msg :=
    { getMsg := id }.

  Definition MEquiv {MsgT} `{HasMsg MsgT} (m1 m2: MsgT) :=
    mid_from (msg_id (getMsg m1)) = mid_from (msg_id (getMsg m1)) /\
    mid_to (msg_id (getMsg m1)) = mid_to (msg_id (getMsg m1)) /\
    mid_chn (msg_id (getMsg m1)) = mid_chn (msg_id (getMsg m1)).
  
End HasMsg.

Infix "≡m" := MEquiv (at level 30).

Definition intOuts {MsgT} `{HasMsg MsgT} (sys: System) (outs: list MsgT) :=
  filter (fun m => isInternal sys (mid_to (msg_id (getMsg m)))) outs.
Definition extOuts {MsgT} `{HasMsg MsgT} (sys: System) (outs: list MsgT) :=
  filter (fun m => isExternal sys (mid_to (msg_id (getMsg m)))) outs.

Section Messages.
  Variable (MsgT: Type).
  Context `{HasMsg MsgT}.

  Definition Queue := list MsgT.
  Definition Channels := M.t (* channel index *) Queue.
  Definition MsgsFrom := M.t (* from *) Channels.
  Definition Messages := M.t (* to *) MsgsFrom.

  Definition firstQ (q: Queue) := hd_error q.
  Definition deq (q: Queue): Queue := tl q.
  Definition enq (m: MsgT) (q: Queue): Queue := q ++ (m :: nil).
  Definition EmptyQ (q: Queue) := q = nil.

  Definition findC (chn: IdxT) (cs: Channels): Queue :=
    ol2l cs@[chn].
  Definition firstC (chn: IdxT) (cs: Channels) :=
    cs@[chn] >>= (fun q => firstQ q).
  Definition deqC (chn: IdxT) (cs: Channels): Channels :=
    match cs@[chn] with
    | Some q => cs +[chn <- deq q]
    | None => cs
    end.
  Definition enqC (chn: IdxT) (m: MsgT) (cs: Channels): Channels :=
    match cs@[chn] with
    | Some q => cs +[chn <- enq m q]
    | None => cs +[chn <- enq m nil]
    end.
  Definition EmptyC (cs: Channels) := forall chn, EmptyQ (findC chn cs).

  Lemma firstC_Some_inv:
    forall chn cs m, firstC chn cs = Some m ->
                     exists q, cs@[chn] = Some q /\ firstQ q = Some m.
  Proof.
    unfold firstC; intros.
    destruct cs@[chn]; simpl in *; [|discriminate].
    eexists; split; auto.
  Qed.

  Definition findMF (from chn: IdxT) (mf: MsgsFrom): Queue :=
    ol2l (mf@[from] >>= (fun cs => cs@[chn])).
  Definition firstMF (from chn: IdxT) (mf: MsgsFrom) :=
    mf@[from] >>= (fun cs => firstC chn cs).
  Definition deqMF (from chn: IdxT) (mf: MsgsFrom): MsgsFrom :=
    match mf@[from] with
    | Some cs => mf +[from <- deqC chn cs]
    | None => mf
    end.
  Definition enqMF (from chn: IdxT) (m: MsgT) (mf: MsgsFrom): MsgsFrom :=
    match mf@[from] with
    | Some cs => mf +[from <- enqC chn m cs]
    | None => mf +[from <- enqC chn m (M.empty _)]
    end.
  Definition EmptyMF (mf: MsgsFrom) :=
    forall from chn, EmptyQ (findMF from chn mf).

  Lemma firstMF_Some_inv:
    forall from chn mf m, firstMF from chn mf = Some m ->
                          exists cs, mf@[from] = Some cs /\ firstC chn cs = Some m.
  Proof.
    unfold firstMF; intros.
    destruct mf@[from]; simpl in *; [|discriminate].
    eexists; split; auto.
  Qed.

  Definition findM (from to chn: IdxT) (msgs: Messages): Queue :=
    ol2l (msgs@[to] >>= (fun froms => froms@[from] >>= (fun cs => cs@[chn]))). 
  Definition firstM (from to chn: IdxT) (msgs: Messages) :=
    msgs@[to] >>= (fun froms => firstMF from chn froms).
  Definition deqM (from to chn: IdxT) (msgs: Messages): Messages :=
    match msgs@[to] with
    | Some froms => msgs +[to <- deqMF from chn froms]
    | None => msgs
    end.
  Definition enqM (from to chn: IdxT) (m: MsgT) (msgs: Messages): Messages :=
    match msgs@[to] with
    | Some froms => msgs +[to <- enqMF from chn m froms]
    | None => msgs +[to <- enqMF from chn m (M.empty _)]
    end.
  
  Definition EmptyM (msgs: Messages) :=
    forall from to chn, EmptyQ (findM from to chn msgs).
  Definition InM (msg: MsgT) (msgs: Messages) :=
    exists from to chn, In msg (findM from to chn msgs).

  Lemma firstM_Some_inv:
    forall from to chn msgs m, firstM from to chn msgs = Some m ->
                               exists mf, msgs@[to] = Some mf /\ firstMF from chn mf = Some m.
  Proof.
    unfold firstM; intros.
    destruct msgs@[to]; simpl in *; [|discriminate].
    eexists; split; auto.
  Qed.

  Definition distributeMsg (msg: MsgT) (msgs: Messages): Messages :=
    enqM (mid_from (msg_id (getMsg msg)))
         (mid_to (msg_id (getMsg msg)))
         (mid_chn (msg_id (getMsg msg))) msg msgs.

  Fixpoint distributeMsgs (nmsgs: list MsgT) (msgs: Messages): Messages :=
    match nmsgs with
    | nil => msgs
    | msg :: nmsgs' =>
      distributeMsg msg (distributeMsgs nmsgs' msgs)
    end.
  
End Messages.

Section Validness.

  Definition ValidMsgId (from to chn: IdxT) {MsgT} `{HasMsg MsgT} (msg: MsgT) :=
    mid_from (msg_id (getMsg msg)) = from /\
    mid_to (msg_id (getMsg msg)) = to /\
    mid_chn (msg_id (getMsg msg)) = chn.

  (* A set of messages are "valid outputs" if
   * 1) they are from the same source [idx],
   * 2) each target is not the source, and
   * 3) all targets (pair of msgTo and channel) are different to each others.
   *)
  Definition ValidOuts (idx: IdxT) {MsgT} `{HasMsg MsgT} (msgs: list MsgT) :=
    Forall (fun m => mid_from (msg_id (getMsg m)) = idx /\
                     mid_to (msg_id (getMsg m)) <> idx) msgs /\
    NoDup (map (fun m => (mid_to (msg_id (getMsg m)), mid_chn (msg_id (getMsg m)))) msgs).

End Validness.

Section HasLabel.

  Inductive Label :=
  | LblIn (min: Msg): Label
  | LblOuts (mouts: list Msg): Label.

  Class HasLabel (LabelT: Type) :=
    { getLabel: LabelT -> Label }.

  Definition emptyLabel := LblOuts nil.

  Definition isEmptyLabel: forall l, {l = emptyLabel} + {l <> emptyLabel}.
  Proof.
    destruct l; [right; discriminate|].
    destruct mouts; [|right; discriminate].
    left; reflexivity.
  Defined.

End HasLabel.

Section HasInit.

  Class HasInit (StateT: Type) :=
    { getStateInit: System -> StateT }.

End HasInit.

Section Transition.

  Definition Step StateT LabelT :=
    System -> StateT -> LabelT -> StateT -> Prop.

  Definition Steps StateT LabelT :=
    System -> StateT -> list LabelT -> StateT -> Prop.

  (* NOTE: the head is the youngest *)
  Inductive steps {StateT LabelT} (step: Step StateT LabelT)
            (sys: System) : StateT -> list LabelT -> StateT -> Prop :=
  | StepsNil: forall st, steps step sys st nil st
  | StepsCons:
      forall st1 ll st2,
        steps step sys st1 ll st2 ->
        forall lbl st3,
          step sys st2 lbl st3 ->
          steps step sys st1 (lbl :: ll) st3.

  Definition psteps {StateT LabelT} (step: Step StateT LabelT)
             (P: StateT -> list LabelT -> StateT -> Prop)
             (sys: System) (st1: StateT) (ll: list LabelT) (st2: StateT) :=
    steps step sys st1 ll st2 /\
    P st1 ll st2.

  Definition extLabel (sys: System) (l: Label) :=
    match l with
    | LblIn _ => Some l
    | LblOuts mouts =>
      match extOuts sys mouts with
      | nil => None
      | _ => Some (LblOuts (extOuts sys mouts))
      end
    end.

  Definition Trace := list Label.

  Fixpoint behaviorOf (sys: System)
           {LabelT} `{HasLabel LabelT} (ll: list LabelT): Trace :=
    match ll with
    | nil => nil
    | l :: ll' => (extLabel sys (getLabel l)) ::> (behaviorOf sys ll')
    end.

  Inductive Behavior {StateT LabelT} `{HasInit StateT} `{HasLabel LabelT}
            (ss: Steps StateT LabelT) : System -> Trace -> Prop :=
  | Behv: forall sys ll st,
      ss sys (getStateInit sys) ll st ->
      forall tr,
        tr = behaviorOf sys ll ->
        Behavior ss sys tr.

  Inductive Reachable {StateT LabelT} `{HasInit StateT} `{HasLabel LabelT}
            (ss: Steps StateT LabelT) : System -> StateT -> Prop :=
  | Rch: forall sys ll st,
      ss sys (getStateInit sys) ll st ->
      Reachable ss sys st.

  Definition Refines {StateI LabelI StateS LabelS}
             `{HasInit StateI} `{HasLabel LabelI} `{HasInit StateS} `{HasLabel LabelS}
             (ssI: Steps StateI LabelI) (ssS: Steps StateS LabelS)
             (p: Label -> Label) (impl spec: System) :=
    forall ll, Behavior ssI impl ll ->
               Behavior ssS spec (map p ll).

End Transition.

Notation "StI # StS |-- I <=[ P ] S" := (Refines StI StS P I S) (at level 30).
Notation "StI # StS |-- I ⊑[ P ] S" := (Refines StI StS P I S) (at level 30).
Notation "StI # StS |-- I <= S" := (Refines StI StS id I S) (at level 30).
Notation "StI # StS |-- I ⊑ S" := (Refines StI StS id I S) (at level 30).

(** Some concrete state and label definitions *)

Section SState.

  Definition ObjectStates := M.t OState.

  Definition getObjectStateInit (obj: Object): OState :=
    {| ost_st := obj_state_init obj;
       ost_tst := trsHelperInit |}.

  Fixpoint getObjectStatesInit (obs: list Object): ObjectStates :=
    match obs with
    | nil => M.empty _
    | obj :: sys' => (getObjectStatesInit sys')
                     +[obj_idx obj <- getObjectStateInit obj]
    end.

  Record SState MsgT :=
    { st_oss: ObjectStates;
      st_msgs: Messages MsgT
    }.

  Definition getSStateInit {MsgT} (sys: System): SState MsgT :=
    {| st_oss := getObjectStatesInit (sys_objs sys);
       st_msgs := [] |}.

  Global Instance SState_HasInit {MsgT} : HasInit (SState MsgT) :=
    { getStateInit := getSStateInit }.

End SState.

Definition MState := SState Msg.

(* [ILabel] represents "internal labels" that reveal 
 * which message is being handled now.
 *)
Section ILabel.

  Inductive ILabel MsgT :=
  | IlblIn (min: MsgT): ILabel MsgT
  | IlblOuts (mhdl: option MsgT) (mouts: list MsgT): ILabel MsgT.

  Definition iLblHdl {MsgT} (l: ILabel MsgT) :=
    match l with
    | IlblIn _ => None
    | IlblOuts mhdl _ => mhdl
    end.

  Definition iLblOuts {MsgT} (l: ILabel MsgT) :=
    match l with
    | IlblIn _ => nil
    | IlblOuts _ mouts => mouts
    end.

  Definition iToLabel {MsgT} `{HasMsg MsgT}
             (l: ILabel MsgT): Label :=
    match l with
    | IlblIn min => LblIn (getMsg min)
    | IlblOuts _ mouts => LblOuts (map getMsg mouts)
    end.

  Global Instance ILabel_HasLabel {MsgT} `{HasMsg MsgT}: HasLabel (ILabel MsgT) :=
    { getLabel := iToLabel }.

  Definition emptyILabel {MsgT} := IlblOuts (MsgT:= MsgT) None nil.

End ILabel.

Section TMsg.

  Definition TrsId := nat.
  Definition trsIdInit: TrsId := 0.

  Record TInfo :=
    { tinfo_tid : TrsId; (* a unique transaction id, assigned when the transaction starts. *)
      tinfo_rqin : Msg
    }.

  Record TMsg :=
    { tmsg_msg : Msg;
      tmsg_info : option TInfo;
    }.

  Definition toTMsg tinfo m :=
    {| tmsg_msg := m;
       tmsg_info := Some tinfo |}.
  Definition toTMsgs tinfo msgs := map (toTMsg tinfo) msgs.

  Definition toTMsgU m := {| tmsg_msg := m; tmsg_info := None |}.

  Global Instance TMsg_HsgMsg : HasMsg TMsg :=
    { getMsg := tmsg_msg }.

  Definition tmsg_dec : forall m1 m2 : TMsg, {m1 = m2} + {m1 <> m2}.
  Proof.
    decide equality.
    - do 2 decide equality.
      + apply msg_dec.
      + decide equality.
    - apply msg_dec.
  Defined.

  Definition TLabel := ILabel TMsg.

  Definition History := list TLabel.

  Definition SubHistory (shst hst: History) :=
    exists nhst, hst = nhst ++ shst.

End TMsg.

Section TState.

  Record TState :=
    { tst_oss: ObjectStates;
      tst_msgs: Messages TMsg;
      tst_tid: TrsId
    }.

  Definition getTStateInit (sys: System): TState :=
    {| tst_oss := getObjectStatesInit (sys_objs sys);
       tst_msgs := [];
       tst_tid := trsIdInit |}.

  Global Instance TState_HasInit: HasInit TState :=
    { getStateInit := getTStateInit }.

End TState.

