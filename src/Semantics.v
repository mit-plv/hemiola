Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax.

Require Export MessagePool.

Set Implicit Arguments.

Open Scope list.

Definition extRqsOf {StateT MsgT} `{HasMsg MsgT}
           (sys: System StateT) (mp: MessagePool MsgT) :=
  qsOf (sys_merqs sys) mp.

Definition extRssOf {StateT MsgT} `{HasMsg MsgT}
           (sys: System StateT) (mp: MessagePool MsgT) :=
  qsOf (sys_merss sys) mp.

Section Validness.
  Context {MsgT: Type} {oifc: OStateIfc}.

  (* A set of messages are "well-distributed" iff the sources of
   * all messages are different from each others.
   *)
  Definition WellDistrMsgs (msgs: list (Id MsgT)) :=
    NoDup (idsOf msgs).

  (* A set of messages are "valid internal inputs" iff
   * 1) each source is internal and
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsIn (sys: System oifc) (msgs: list (Id MsgT)) :=
    SubList (idsOf msgs) (sys_minds sys ++ sys_merqs sys) /\
    WellDistrMsgs msgs.

  (* A set of messages are "valid outputs" iff
   * 1) each message is using either an internal or
   *    an external-response queue.
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsOut (sys: System oifc) (msgs: list (Id MsgT)) :=
    SubList (idsOf msgs) (sys_minds sys ++ sys_merss sys) /\
    WellDistrMsgs msgs.

  (* A set of messages are "valid external inputs" iff
   * 1) each message uses an external request queue and
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsExtIn (sys: System oifc) (msgs: list (Id MsgT)) :=
    SubList (idsOf msgs) (sys_merqs sys) /\
    WellDistrMsgs msgs.

  (* A set of messages are "valid external outputs" iff
   * 1) each message uses an external response queue and
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsExtOut (sys: System oifc) (msgs: list (Id MsgT)) :=
    SubList (idsOf msgs) (sys_merss sys) /\
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
  Variables (SystemT StateT LabelT: Type).

  Definition Step := SystemT -> StateT -> LabelT -> StateT -> Prop.
  Definition Steps := SystemT -> StateT -> list LabelT -> StateT -> Prop.

  (* NOTE: the head is the youngest *)
  Inductive steps (step: Step) (sys: SystemT): StateT -> list LabelT -> StateT -> Prop :=
  | StepsNil: forall st, steps step sys st nil st
  | StepsCons:
      forall st1 ll st2,
        steps step sys st1 ll st2 ->
        forall lbl st3,
          step sys st2 lbl st3 ->
          steps step sys st1 (lbl :: ll) st3.

  Definition psteps (step: Step)
             (P: StateT -> list LabelT -> StateT -> Prop)
             (sys: SystemT) (st1: StateT) (ll: list LabelT) (st2: StateT) :=
    steps step sys st1 ll st2 /\
    P st1 ll st2.

End Transition.

Section Behavior.

  Definition Trace := list Label.

  Definition Reachable {SystemT StateT LabelT} `{HasInit SystemT StateT} `{HasLabel LabelT}
             (ss: Steps SystemT StateT LabelT) (sys: SystemT) (st: StateT): Prop :=
    exists ll, ss sys (initsOf sys) ll st.
  
  Fixpoint behaviorOf {LabelT} `{HasLabel LabelT} (ll: list LabelT): Trace :=
    match ll with
    | nil => nil
    | l :: ll' => (getLabel l) ::> (behaviorOf ll')
    end.

  Inductive Behavior {SystemT StateT LabelT} `{HasInit SystemT StateT} `{HasLabel LabelT}
            (ss: Steps SystemT StateT LabelT) : SystemT -> Trace -> Prop :=
  | Behv: forall sys ll st,
      ss sys (initsOf sys) ll st ->
      forall tr,
        tr = behaviorOf ll ->
        Behavior ss sys tr.

  Definition Refines {SystemI StateI LabelI SystemS StateS LabelS}
             `{HasInit SystemI StateI} `{HasInit SystemS StateS}
             `{HasLabel LabelI} `{HasLabel LabelS}
             (ssI: Steps SystemI StateI LabelI) (ssS: Steps SystemS StateS LabelS)
             (impl: SystemI) (spec: SystemS) :=
    forall tr, Behavior ssI impl tr ->
               Behavior ssS spec tr.

End Behavior.

Notation "StI # StS |-- I <= S" := (Refines StI StS I S) (at level 30).
Notation "StI # StS |-- I ⊑ S" := (Refines StI StS I S) (at level 30).

(** Some concrete state and label definitions *)

(* A basis state with [Msg]s. *)
Record MState oifc :=
  { bst_oss: OStates oifc;
    bst_orqs: ORqs Msg;
    bst_msgs: MessagePool Msg
  }.

Definition getMStateInit {oifc} (sys: System oifc): MState oifc :=
  {| bst_oss := initsOf sys;
     bst_orqs := M.empty _;
     bst_msgs := emptyMP _ |}.

Global Instance MState_HasInit {oifc}: HasInit (System oifc) (MState oifc) :=
  {| initsOf := getMStateInit |}.

Definition IntMsgsEmpty {oifc} (sys: System oifc) (msgs: MessagePool Msg) :=
  forall midx,
    In midx sys.(sys_minds) ->
    findQ midx msgs = nil.

(* [RLabel] represents "internal rule-driven labels" that reveal which message 
 * is being handled now.
 *)
Section RLabel.
  Variable MsgT: Type.
  Context `{HasMsg MsgT}.

  Inductive RLabel :=
  | RlblEmpty
  | RlblIns (mins: list (Id MsgT)): RLabel
  | RlblInt (oidx ridx: IdxT) (mins: list (Id MsgT)) (mouts: list (Id MsgT)): RLabel
  | RlblOuts (mouts: list (Id MsgT)): RLabel.
  
  Definition rToLabel (l: RLabel): option Label :=
    match l with
    | RlblEmpty => None
    | RlblIns mins => Some (LblIns (imap getMsg mins))
    | RlblInt _ _ _ _ => None
    | RlblOuts mouts => Some (LblOuts (imap getMsg mouts))
    end.

  Global Instance RLabel_HasLabel: HasLabel RLabel :=
    { getLabel := rToLabel }.

End RLabel.

Definition MLabel := RLabel Msg.
Definition History (MsgT: Type) := list (RLabel MsgT).

Definition MHistory := History Msg.

Definition WfLbl {oifc} (sys: System oifc) (lbl: MLabel) :=
  match lbl with
  | RlblEmpty _ => True
  | RlblIns eins => eins <> nil /\ ValidMsgsExtIn sys eins
  | RlblOuts eouts => eouts <> nil /\ ValidMsgsExtOut sys eouts
  | RlblInt oidx ridx ins outs =>
    exists obj rule,
    In obj (sys_objs sys) /\ obj_idx obj = oidx /\
    In rule (obj_rules obj) /\ rule_idx rule = ridx /\
    ValidMsgsIn sys ins /\
    ValidMsgsOut sys outs /\
    DisjList (idsOf ins) (idsOf outs)
  end.

Definition WfHistory {oifc} (sys: System oifc) (hst: MHistory) :=
  Forall (WfLbl sys) hst.

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

Record TState ifc :=
  { tst_oss: OStates ifc;
    tst_orqs: ORqs TMsg;
    tst_msgs: MessagePool TMsg;
    tst_trss: MessagePool TMsg;
    tst_tid: TrsId
  }.

Close Scope list.

