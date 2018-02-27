Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax.

Set Implicit Arguments.

Definition intOuts {OState ObjT SysT MsgT} `{HasObjects OState ObjT SysT} `{HasMsg MsgT}
           (sys: SysT) (outs: list MsgT) :=
  filter (fun m => isInternal sys (mid_to (msg_id (getMsg m)))) outs.
Definition extOuts {OState ObjT SysT MsgT} `{HasObjects OState ObjT SysT} `{HasMsg MsgT}
           (sys: SysT) (outs: list MsgT) :=
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

  Definition removeMP (m: MsgT) (mp: MessagePool): MessagePool :=
    let mid := msg_id (getMsg m) in
    deqMP (mid_from mid) (mid_to mid) (mid_chn mid) mp.

  Definition FirstMP (mp: MessagePool) (m: MsgT) :=
    let mid := msg_id (getMsg m) in
    firstMP (mid_from mid) (mid_to mid) (mid_chn mid) mp = Some m.
             
  Definition EmptyMP (mp: MessagePool) := mp = nil.
  Definition InMP (msg: MsgT) (mp: MessagePool) := In msg mp.

  Definition ForallMP (P: MsgT -> Prop) (mp: MessagePool) :=
    Forall P mp.

  Definition distributeMsgs (nmsgs: list MsgT) (mp: MessagePool): MessagePool :=
    mp ++ nmsgs.

  Fixpoint removeMsgs (dmsgs: list MsgT) (mp: MessagePool): MessagePool :=
    match dmsgs with
    | nil => mp
    | dmsg :: dmsgs' =>
      removeMsgs dmsgs' (removeMP dmsg mp)
    end.
  
End MessagePool.

Section Validness.

  Definition ValidMsgId (from to chn: IdxT) {MsgT} `{HasMsg MsgT} (msg: MsgT) :=
    mid_addr (msg_id (getMsg msg)) = buildMsgAddr from to chn.

  (* A set of messages are "valid outputs" if
   * 1) they are from the same source [idx],
   * 2) each target is not the source, and
   * 3) all targets (pair of msgTo and channel) are different to each others.
   *)
  Definition ValidMsgOuts (idx: IdxT) {MsgT} `{HasMsg MsgT} (msgs: list MsgT) :=
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
  Variable OState: Type.

  Class HasInit (SysT: Type) (StateT: Type) :=
    { getStateInit: SysT -> StateT }.

  Definition ObjectStates := M.t OState.

  Fixpoint getObjectStatesInit {ObjT} `{IsObject OState ObjT}
           (obs: list ObjT): ObjectStates :=
    match obs with
    | nil => M.empty _
    | obj :: obs' => (getObjectStatesInit obs') +[getIndex obj <- getOStateInit obj]
    end.

  Global Instance HasObjects_HasInit {ObjT SysT} `{HasObjects OState ObjT SysT}
    : HasInit SysT ObjectStates :=
    {| getStateInit := fun sys => getObjectStatesInit (getObjects sys) |}.

End HasInit.

Section Transition.

  Definition Step SysT StateT LabelT :=
    SysT -> StateT -> LabelT -> StateT -> Prop.

  Definition Steps SysT StateT LabelT :=
    SysT -> StateT -> list LabelT -> StateT -> Prop.

  (* NOTE: the head is the youngest *)
  Inductive steps {SysT StateT LabelT} `{HasInit SysT StateT}
            (step: Step SysT StateT LabelT)
            (sys: SysT) : StateT -> list LabelT -> StateT -> Prop :=
  | StepsNil: forall st, steps step sys st nil st
  | StepsCons:
      forall st1 ll st2,
        steps step sys st1 ll st2 ->
        forall lbl st3,
          step sys st2 lbl st3 ->
          steps step sys st1 (lbl :: ll) st3.

  Definition psteps {SysT StateT LabelT} `{HasInit SysT StateT}
             (step: Step SysT StateT LabelT)
             (P: StateT -> list LabelT -> StateT -> Prop)
             (sys: SysT) (st1: StateT) (ll: list LabelT) (st2: StateT) :=
    steps step sys st1 ll st2 /\
    P st1 ll st2.

  Definition extLabel {OState ObjT SysT} `{HasObjects OState ObjT SysT}
             (sys: SysT) (l: Label) :=
    match l with
    | LblIn _ => Some l
    | LblOuts mouts =>
      match extOuts sys mouts with
      | nil => None
      | _ => Some (LblOuts (extOuts sys mouts))
      end
    end.

  Definition Trace := list Label.

  Fixpoint behaviorOf {OState ObjT SysT} `{HasObjects OState ObjT SysT} (sys: SysT)
           {LabelT} `{HasLabel LabelT} (ll: list LabelT): Trace :=
    match ll with
    | nil => nil
    | l :: ll' => (extLabel sys (getLabel l)) ::> (behaviorOf sys ll')
    end.

  Inductive Behavior {OState ObjT SysT StateT LabelT}
            `{HasObjects OState ObjT SysT} `{HasInit SysT StateT} `{HasLabel LabelT}
            (ss: Steps SysT StateT LabelT) : SysT -> Trace -> Prop :=
  | Behv: forall sys ll st,
      ss sys (getStateInit sys) ll st ->
      forall tr,
        tr = behaviorOf sys ll ->
        Behavior ss sys tr.

  Definition Refines {OState ObjT SysT StateI LabelI StateS LabelS}
             `{HasObjects OState ObjT SysT}
             `{HasInit SysT StateI} `{HasLabel LabelI}
             `{HasInit SysT StateS} `{HasLabel LabelS}
             (ssI: Steps SysT StateI LabelI) (ssS: Steps SysT StateS LabelS)
             (p: Label -> Label) (impl spec: SysT) :=
    forall ll, Behavior ssI impl ll ->
               Behavior ssS spec (map p ll).

End Transition.

Notation "StI # StS |-- I <=[ P ] S" := (Refines StI StS P I S) (at level 30).
Notation "StI # StS |-- I ⊑[ P ] S" := (Refines StI StS P I S) (at level 30).
Notation "StI # StS |-- I <= S" := (Refines StI StS id I S) (at level 30).
Notation "StI # StS |-- I ⊑ S" := (Refines StI StS id I S) (at level 30).

(** Some concrete state and label definitions *)

(* Ordinary states with [Msg]s. *)
Section OrdState.

  Definition OrdOState := M.t Value.

  Record OrdState MsgT :=
    { mst_oss: ObjectStates OrdOState;
      mst_msgs: MessagePool MsgT
    }.

  Definition getOrdStateInit {MsgT} (sys: System OrdOState): OrdState MsgT :=
    {| mst_oss := getObjectStatesInit sys;
       mst_msgs := nil |}.

  Global Instance OrdState_HasInit {MsgT} : HasInit (System OrdOState) (OrdState MsgT) :=
    { getStateInit := getOrdStateInit }.

End OrdState.

Definition MState := OrdState Msg.

(* [RLabel] represents "internal rule-driven labels" that reveal which message 
 * is being handled now.
 *)
Section RLabel.

  Inductive RLabel MsgT :=
  | IlblIn (min: MsgT): RLabel MsgT
  | IlblOuts (hdl: option (Rule OrdOState)) (mins: list MsgT) (mouts: list MsgT): RLabel MsgT.

  Definition iLblIns {MsgT} (l: RLabel MsgT) :=
    match l with
    | IlblIn _ => nil
    | IlblOuts _ mins _ => mins
    end.

  Definition iLblOuts {MsgT} (l: RLabel MsgT) :=
    match l with
    | IlblIn _ => nil
    | IlblOuts _ _ mouts => mouts
    end.

  Definition iToLabel {MsgT} `{HasMsg MsgT}
             (l: RLabel MsgT): Label :=
    match l with
    | IlblIn min => LblIn (getMsg min)
    | IlblOuts _ _ mouts => LblOuts (map getMsg mouts)
    end.

  Global Instance RLabel_HasLabel {MsgT} `{HasMsg MsgT}: HasLabel (RLabel MsgT) :=
    { getLabel := iToLabel }.

  Definition emptyRLabel {MsgT} := IlblOuts (MsgT:= MsgT) None nil nil.

End RLabel.

Section TMsg.

  Definition TrsId := nat.
  Definition trsIdInit: TrsId := 0.

  Record TInfo :=
    { (* a unique transaction id, assigned when the transaction starts. *)
      tinfo_tid : TrsId; 
      tinfo_rqin : list Msg
    }.

  Definition buildTInfo tid rqin :=
    {| tinfo_tid := tid; tinfo_rqin := rqin |}.

  Definition tinfo_dec : forall ti1 ti2: TInfo, {ti1 = ti2} + {ti1 <> ti2}.
  Proof.
    decide equality.
    - decide equality.
      apply msg_dec.
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

  Definition TLabel := RLabel TMsg.
  Definition THistory := list TLabel.

End TMsg.

Section TState.

  Record TState :=
    { tst_oss: ObjectStates OrdOState;
      tst_msgs: MessagePool TMsg;
      tst_tid: TrsId
    }.

  Definition getTStateInit (sys: System OrdOState): TState :=
    {| tst_oss := getObjectStatesInit sys;
       tst_msgs := nil;
       tst_tid := trsIdInit |}.

  Global Instance TState_HasInit: HasInit (System OrdOState) TState :=
    { getStateInit := getTStateInit }.

End TState.

