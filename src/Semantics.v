Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax.

Require Export MessagePool.

Set Implicit Arguments.

Definition extRqsOf {MsgT SysT} `{HasMsg MsgT} `{IsSystem SysT}
           (sys: SysT) (mp: MessagePool MsgT) :=
  qsOf (merqsOf sys) mp.

Definition extRssOf {MsgT SysT} `{HasMsg MsgT} `{IsSystem SysT}
           (sys: SysT) (mp: MessagePool MsgT) :=
  qsOf (merssOf sys) mp.

Section Validness.
  Context {MsgT SysT: Type} `{IsSystem SysT}.

  (* A set of messages are "well-distributed" iff the sources of
   * all messages are different from each others.
   *)
  Definition WellDistrMsgs (msgs: list (Id MsgT)) :=
    NoDup (idsOf msgs).

  (* A set of messages are "valid internal inputs" iff
   * 1) each source is internal and
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsIn (sys: SysT) (msgs: list (Id MsgT)) :=
    SubList (idsOf msgs) (mindsOf sys) /\
    WellDistrMsgs msgs.

  (* A set of messages are "valid outputs" iff
   * 1) each message is using either an internal or
   *    an external-response queue.
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsOut (sys: SysT) (msgs: list (Id MsgT)) :=
    SubList (idsOf msgs) (mindsOf sys ++ merssOf sys) /\
    WellDistrMsgs msgs.

  (* A set of messages are "valid external inputs" iff
   * 1) each message uses an external request queue and
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsExtIn (sys: SysT) (msgs: list (Id MsgT)) :=
    SubList (idsOf msgs) (merqsOf sys) /\
    WellDistrMsgs msgs.

  (* A set of messages are "valid external outputs" iff
   * 1) each message uses an external response queue and
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsExtOut (sys: SysT) (msgs: list (Id MsgT)) :=
    SubList (idsOf msgs) (merssOf sys) /\
    WellDistrMsgs msgs.

End Validness.

Section HasLabel.

  Inductive Label :=
  | LblIns (mins: list (Id Msg)): Label
  | LblOuts (mouts: list (Id Msg)): Label.

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
             (impl: SysI) (spec: SysS) :=
    forall ll, Behavior ssI impl ll ->
               Behavior ssS spec ll.

End Transition.

Notation "StI # StS |-- I <= S" := (Refines StI StS I S) (at level 30).
Notation "StI # StS |-- I ⊑ S" := (Refines StI StS I S) (at level 30).

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
       bst_msgs := emptyMP _ |}.

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
  | RlblEmpty
  | RlblIns (mins: list (Id MsgT)): RLabel
  | RlblInt (hdl: Rule) (mins: list (Id MsgT)) (mouts: list (Id MsgT)): RLabel
  | RlblOuts (mouts: list (Id MsgT)): RLabel.
  
  Definition rToLabel (l: RLabel): option Label :=
    match l with
    | RlblEmpty => None
    | RlblIns mins => Some (LblIns (imap getMsg mins))
    | RlblInt _ _ _ => None
    | RlblOuts mouts => Some (LblOuts (imap getMsg mouts))
    end.

  Global Instance RLabel_HasLabel: HasLabel RLabel :=
    { getLabel := rToLabel }.

End RLabel.

Definition MLabel := RLabel Msg.
Definition History (MsgT: Type) := list (RLabel MsgT).

Definition MHistory := History Msg.

Section TMsg.

  Definition TrsId := nat.
  Definition trsIdInit: TrsId := 0.

  Record TInfo :=
    { (* a unique transaction id, assigned when the transaction starts. *)
      tinfo_tid : TrsId; 
      tinfo_rqin : list (Id Msg)
    }.

  Definition buildTInfo tid rqin :=
    {| tinfo_tid := tid; tinfo_rqin := rqin |}.

  Definition tinfo_dec : forall ti1 ti2: TInfo, {ti1 = ti2} + {ti1 <> ti2}.
  Proof.
    decide equality.
    - decide equality.
      decide equality.
      + apply msg_dec.
      + decide equality.
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

  Definition liftTmap (mmap: Msg -> Msg): TMsg -> TMsg :=
    fun tmsg =>
      {| tmsg_msg := mmap (tmsg_msg tmsg);
         tmsg_info := tmsg_info tmsg
      |}.

End TMsg.

Section TState.

  Record TState :=
    { tst_oss: OStates;
      tst_orqs: ORqs TMsg;
      tst_msgs: MessagePool TMsg;
      tst_trss: MessagePool TMsg;
      tst_tid: TrsId
    }.

  Context {SysT: Type} `{IsSystem SysT} `{HasInit SysT OStates}.

  Definition getTStateInit (sys: SysT): TState :=
    {| tst_oss := initsOf sys;
       tst_orqs := initsOf sys;
       tst_msgs := emptyMP _;
       tst_trss := emptyMP _;
       tst_tid := trsIdInit |}.

  Global Instance TState_HasInit: HasInit SysT TState :=
    {| initsOf := getTStateInit |}.

End TState.

