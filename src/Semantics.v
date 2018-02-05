Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax.

Set Implicit Arguments.

Section HasMsg.
  Class HasMsg (MsgT: Type) :=
    { getMsg : MsgT -> Msg }.

  Global Instance Msg_HasMsg : HasMsg Msg :=
    { getMsg := id }.

End HasMsg.

Definition intOuts {MsgT} `{HasMsg MsgT} (sys: System) (outs: list MsgT) :=
  filter (fun m => isInternal sys (mid_to (msg_id (getMsg m)))) outs.
Definition extOuts {MsgT} `{HasMsg MsgT} (sys: System) (outs: list MsgT) :=
  filter (fun m => isExternal sys (mid_to (msg_id (getMsg m)))) outs.

Section MessagePool.
  Variable (MsgT: Type).
  Context `{HasMsg MsgT}.

  Definition Queue := list MsgT.
  Definition MessagePool := list MsgT.

  Definition findMP (from to chn: IdxT) (mp: MessagePool): Queue :=
    filter (fun msg =>
              if msgAddr_dec (mid_addr (msg_id (getMsg msg))) (buildMsgAddr from to chn)
              then true
              else false) mp.

  Definition firstMP (from to chn: IdxT) (mp: MessagePool) :=
    hd_error (findMP from to chn mp).

  Fixpoint deqMP (from to chn: IdxT) (mp: MessagePool): MessagePool :=
    match mp with
    | nil => nil
    | msg :: mp' =>
      if msgAddr_dec (mid_addr (msg_id (getMsg msg))) (buildMsgAddr from to chn)
      then mp'
      else msg :: deqMP from to chn mp'
    end.

  Definition enqMP (m: MsgT) (mp: MessagePool): MessagePool := mp ++ (m :: nil).

  Definition FirstMP (mp: MessagePool) (m: MsgT) :=
    let mid := msg_id (getMsg m) in
    firstMP (mid_from mid) (mid_to mid) (mid_chn mid) mp = Some m.
             
  Definition EmptyMP (mp: MessagePool) := mp = nil.
  Definition InMP (msg: MsgT) (mp: MessagePool) := In msg mp.

  Definition ForallMP (P: MsgT -> Prop) (mp: MessagePool) :=
    Forall P mp.

  Definition distributeMsgs (nmsgs: list MsgT) (mp: MessagePool): MessagePool :=
    mp ++ nmsgs.
  
End MessagePool.

Section Validness.

  Definition ValidMsgId (from to chn: IdxT) {MsgT} `{HasMsg MsgT} (msg: MsgT) :=
    mid_addr (msg_id (getMsg msg)) = buildMsgAddr from to chn.

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
      st_msgs: MessagePool MsgT
    }.

  Definition getSStateInit {MsgT} (sys: System): SState MsgT :=
    {| st_oss := getObjectStatesInit sys;
       st_msgs := nil |}.

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

  Definition buildTInfo tid rqin :=
    {| tinfo_tid := tid; tinfo_rqin := rqin |}.

  Definition tinfo_dec : forall ti1 ti2: TInfo, {ti1 = ti2} + {ti1 <> ti2}.
  Proof.
    decide equality.
    - apply msg_dec.
    - decide equality.
  Defined.

  Record TMsg :=
    { tmsg_msg : Msg;
      tmsg_info : option TInfo;
    }.

  Definition tmsg_dec : forall m1 m2 : TMsg, {m1 = m2} + {m1 <> m2}.
  Proof.
    decide equality.
    - decide equality.
      apply tinfo_dec.
    - apply msg_dec.
  Defined.

  Definition toTMsg tinfo m :=
    {| tmsg_msg := m;
       tmsg_info := Some tinfo |}.
  Definition toTMsgs tinfo msgs := map (toTMsg tinfo) msgs.

  Definition toTMsgU m := {| tmsg_msg := m; tmsg_info := None |}.

  Global Instance TMsg_HsgMsg : HasMsg TMsg :=
    { getMsg := tmsg_msg }.

  Definition TLabel := ILabel TMsg.

  Definition History := list TLabel.

End TMsg.

Section TState.

  Record TState :=
    { tst_oss: ObjectStates;
      tst_msgs: MessagePool TMsg;
      tst_tid: TrsId
    }.

  Definition getTStateInit (sys: System): TState :=
    {| tst_oss := getObjectStatesInit sys;
       tst_msgs := nil;
       tst_tid := trsIdInit |}.

  Global Instance TState_HasInit: HasInit TState :=
    { getStateInit := getTStateInit }.

End TState.

