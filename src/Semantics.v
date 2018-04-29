Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax.

Require Export MessagePool.

Set Implicit Arguments.

Definition intOuts {SysT MsgT} `{IsSystem SysT} `{HasMsg MsgT}
           (sys: SysT) (outs: list MsgT) :=
  filter (fun m => toInternal sys m) outs.
Definition extOuts {SysT MsgT} `{IsSystem SysT} `{HasMsg MsgT}
           (sys: SysT) (outs: list MsgT) :=
  filter (fun m => toExternal sys m) outs.

Section Validness.
  Context {MsgT} `{HasMsg MsgT}.

  (* A set of "incoming" messages are "well-distributed" iff
   * all sources (pair of [mid_from] and [mid_chn]) are different from 
   * each others. 
   *)
  Definition WellDistrMsgsIn (msgs: list MsgT) :=
    NoDup (map (fun m => (mid_from (msg_id (getMsg m)),
                          mid_chn (msg_id (getMsg m)))) msgs).

  (* A set of "outgoing" messages are "well-distributed" iff
   * all targets (pair of [mid_to] and [mid_chn]) are different from 
   * each others. 
   *)
  Definition WellDistrMsgsOut (msgs: list MsgT) :=
    NoDup (map (fun m => (mid_to (msg_id (getMsg m)),
                          mid_chn (msg_id (getMsg m)))) msgs).

  (* A set of messages are "valid inputs" iff
   * 1) they have the same target [oidx],
   * 2) each source is not the target, and
   * 3) they are well-distributed.
   *)
  Definition ValidMsgsIn (oidx: IdxT) (msgs: list MsgT) :=
    Forall (fun msg => mid_to (msg_id (getMsg msg)) = oidx /\
                       mid_from (msg_id (getMsg msg)) <> oidx) msgs /\
    WellDistrMsgsIn msgs.

  (* A set of messages are "valid outputs" iff
   * 1) they are from the same source [oidx],
   * 2) each target is not the source, and
   * 3) they are well-distributed.
   *)
  Definition ValidMsgsOut (oidx: IdxT) (msgs: list MsgT) :=
    Forall (fun m => mid_from (msg_id (getMsg m)) = oidx /\
                     mid_to (msg_id (getMsg m)) <> oidx) msgs /\
    WellDistrMsgsOut msgs.

  Context {SysT} `{IsSystem SysT}.
  
  (* A set of messages are "valid external inputs" iff
   * 1) each source is external,
   * 2) each target is internal, and
   * 3) they are well-distributed.
   *)
  Definition ValidMsgsExtIn (sys: SysT) (msgs: list MsgT) :=
    Forall (fun msg => fromExternal sys msg = true /\
                       toInternal sys msg = true) msgs /\
    WellDistrMsgsIn msgs.

  (* A set of messages are "valid external outputs" iff
   * 1) each source is internal,
   * 2) each target is external, and
   * 3) they are well-distributed.
   *)
  Definition ValidMsgsExtOut (sys: SysT) (msgs: list MsgT) :=
    Forall (fun msg => fromInternal sys msg = true /\
                       toExternal sys msg = true) msgs /\
    WellDistrMsgsOut msgs.

End Validness.

Section HasLabel.

  Inductive Label :=
  | LblIns (mins: list Msg): Label
  | LblOuts (mouts: list Msg): Label.

  Class HasLabel (LabelT: Type) :=
    { getLabel: LabelT -> option Label }.

End HasLabel.

Section Transition.

  Definition Step SysT StateT LabelT :=
    SysT -> StateT -> LabelT -> StateT -> Prop.

  Definition Steps SysT StateT LabelT :=
    SysT -> StateT -> list LabelT -> StateT -> Prop.

  (* NOTE: the head is the youngest *)
  Inductive steps {SysT StateT LabelT}
            (step: Step SysT StateT LabelT)
            (sys: SysT) : StateT -> list LabelT -> StateT -> Prop :=
  | StepsNil: forall st, steps step sys st nil st
  | StepsCons:
      forall st1 ll st2,
        steps step sys st1 ll st2 ->
        forall lbl st3,
          step sys st2 lbl st3 ->
          steps step sys st1 (lbl :: ll) st3.

  Definition psteps {SysT StateT LabelT}
             (step: Step SysT StateT LabelT)
             (P: StateT -> list LabelT -> StateT -> Prop)
             (sys: SysT) (st1: StateT) (ll: list LabelT) (st2: StateT) :=
    steps step sys st1 ll st2 /\
    P st1 ll st2.

  Definition Trace := list Label.

  Fixpoint behaviorOf {SysT} `{IsSystem SysT} (sys: SysT)
           {LabelT} `{HasLabel LabelT} (ll: list LabelT): Trace :=
    match ll with
    | nil => nil
    | l :: ll' => (getLabel l) ::> (behaviorOf sys ll')
    end.

  Inductive Behavior {SysT StateT LabelT}
            `{IsSystem SysT} `{HasInit SysT StateT} `{HasLabel LabelT}
            (ss: Steps SysT StateT LabelT) : SysT -> Trace -> Prop :=
  | Behv: forall sys ll st,
      ss sys (initsOf sys) ll st ->
      forall tr,
        tr = behaviorOf sys ll ->
        Behavior ss sys tr.

  Definition Refines {SysI SysS StateI LabelI StateS LabelS}
             `{IsSystem SysI} `{HasInit SysI StateI} `{HasLabel LabelI}
             `{IsSystem SysS} `{HasInit SysS StateS} `{HasLabel LabelS}
             (ssI: Steps SysI StateI LabelI) (ssS: Steps SysS StateS LabelS)
             (p: Label -> Label) (impl: SysI) (spec: SysS) :=
    forall ll, Behavior ssI impl ll ->
               Behavior ssS spec (map p ll).

End Transition.

Notation "StI # StS |-- I <=[ P ] S" := (Refines StI StS P I S) (at level 30).
Notation "StI # StS |-- I ⊑[ P ] S" := (Refines StI StS P I S) (at level 30).
Notation "StI # StS |-- I <= S" := (Refines StI StS id I S) (at level 30).
Notation "StI # StS |-- I ⊑ S" := (Refines StI StS id I S) (at level 30).

(** Some concrete state and label definitions *)

(* A basis state with [Msg]s. *)
Section BState.

  Record BState MsgT :=
    { bst_oss: OStates;
      bst_orqs: ORqs MsgT;
      bst_msgs: MessagePool MsgT
    }.

  Context {SysT: Type} `{IsSystem SysT} `{HasInit SysT OStates}
          {MsgT: Type}.

  Definition getBStateInit (sys: SysT): BState MsgT :=
    {| bst_oss := initsOf sys;
       bst_orqs := initsOf sys;
       bst_msgs := nil |}.

  Global Instance BState_HasInit: HasInit SysT (BState MsgT) :=
    {| initsOf := getBStateInit |}.

End BState.

Definition MState := BState Msg.

(* [RLabel] represents "internal rule-driven labels" that reveal which message 
 * is being handled now.
 *)
Section RLabel.
  Variable MsgT: Type.
  Context `{HasMsg MsgT}.

  Inductive RLabel :=
  | RlblIns (mins: list MsgT): RLabel
  | RlblInt (hdl: option Rule) (mins: list MsgT) (mouts: list MsgT): RLabel
  | RlblOuts (mouts: list MsgT): RLabel.

  Definition emptyRLabel := RlblInt None nil nil.
  
  Definition rToLabel (l: RLabel): option Label :=
    match l with
    | RlblIns mins => Some (LblIns (map getMsg mins))
    | RlblInt _ _ _ => None
    | RlblOuts mouts => Some (LblOuts (map getMsg mouts))
    end.

  Global Instance RLabel_HasLabel: HasLabel RLabel :=
    { getLabel := rToLabel }.

End RLabel.

Definition MLabel := RLabel Msg.
Definition History := list MLabel.

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
  Definition toTMsgsU msgs := map toTMsgU msgs.

  Global Instance TMsg_HsgMsg : HasMsg TMsg :=
    { getMsg := tmsg_msg }.

  Definition TLabel := RLabel TMsg.
  Definition THistory := list TLabel.

  Definition liftMsgP (msgP: Msg -> Msg): TMsg -> TMsg :=
    fun tmsg =>
      {| tmsg_msg := msgP (tmsg_msg tmsg);
         tmsg_info := tmsg_info tmsg
      |}.

End TMsg.

Section TState.

  Record TState :=
    { tst_oss: OStates;
      tst_orqs: ORqs TMsg;
      tst_msgs: MessagePool TMsg;
      tst_tid: TrsId
    }.

  Context {SysT: Type} `{IsSystem SysT} `{HasInit SysT OStates}.

  Definition getTStateInit (sys: SysT): TState :=
    {| tst_oss := initsOf sys;
       tst_orqs := initsOf sys;
       tst_msgs := nil;
       tst_tid := trsIdInit |}.

  Global Instance TState_HasInit: HasInit SysT TState :=
    {| initsOf := getTStateInit |}.

End TState.

