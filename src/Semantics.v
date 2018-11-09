Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax.

Require Export MessagePool.

Set Implicit Arguments.

Open Scope list.

Definition extRqsOf {MsgT} `{HasMsg MsgT}
           (sys: System) (mp: MessagePool MsgT) :=
  qsOf (sys_merqs sys) mp.

Definition extRssOf {MsgT} `{HasMsg MsgT}
           (sys: System) (mp: MessagePool MsgT) :=
  qsOf (sys_merss sys) mp.

Section Validness.
  Context {MsgT: Type}.

  (* A set of messages are "well-distributed" iff the sources of
   * all messages are different from each others.
   *)
  Definition WellDistrMsgs (msgs: list (Id MsgT)) :=
    NoDup (idsOf msgs).

  (* A set of messages are "valid internal inputs" iff
   * 1) each source is internal and
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsIn (sys: System) (msgs: list (Id MsgT)) :=
    SubList (idsOf msgs) (sys_minds sys) /\
    WellDistrMsgs msgs.

  (* A set of messages are "valid outputs" iff
   * 1) each message is using either an internal or
   *    an external-response queue.
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsOut (sys: System) (msgs: list (Id MsgT)) :=
    SubList (idsOf msgs) (sys_minds sys ++ sys_merss sys) /\
    WellDistrMsgs msgs.

  (* A set of messages are "valid external inputs" iff
   * 1) each message uses an external request queue and
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsExtIn (sys: System) (msgs: list (Id MsgT)) :=
    SubList (idsOf msgs) (sys_merqs sys) /\
    WellDistrMsgs msgs.

  (* A set of messages are "valid external outputs" iff
   * 1) each message uses an external response queue and
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsExtOut (sys: System) (msgs: list (Id MsgT)) :=
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

  Definition Step StateT LabelT :=
    System -> StateT -> LabelT -> StateT -> Prop.

  Definition Steps StateT LabelT :=
    System -> StateT -> list LabelT -> StateT -> Prop.

  (* NOTE: the head is the youngest *)
  Inductive steps {StateT LabelT}
            (step: Step StateT LabelT)
            (sys: System) : StateT -> list LabelT -> StateT -> Prop :=
  | StepsNil: forall st, steps step sys st nil st
  | StepsCons:
      forall st1 ll st2,
        steps step sys st1 ll st2 ->
        forall lbl st3,
          step sys st2 lbl st3 ->
          steps step sys st1 (lbl :: ll) st3.

  Definition psteps {StateT LabelT}
             (step: Step StateT LabelT)
             (P: StateT -> list LabelT -> StateT -> Prop)
             (sys: System) (st1: StateT) (ll: list LabelT) (st2: StateT) :=
    steps step sys st1 ll st2 /\
    P st1 ll st2.

End Transition.

Section Behavior.
  
  Definition Trace := list Label.

  Definition Reachable {StateT LabelT}
             `{HasInit System StateT} `{HasLabel LabelT}
             (ss: Steps StateT LabelT) (sys: System) (st: StateT): Prop :=
    exists ll, ss sys (initsOf sys) ll st.
  
  Fixpoint behaviorOf {LabelT} `{HasLabel LabelT} (ll: list LabelT): Trace :=
    match ll with
    | nil => nil
    | l :: ll' => (getLabel l) ::> (behaviorOf ll')
    end.

  Inductive Behavior {StateT LabelT}
            `{HasInit System StateT} `{HasLabel LabelT}
            (ss: Steps StateT LabelT) : System -> Trace -> Prop :=
  | Behv: forall sys ll st,
      ss sys (initsOf sys) ll st ->
      forall tr,
        tr = behaviorOf ll ->
        Behavior ss sys tr.

  Definition Refines {StateI LabelI StateS LabelS}
             `{HasInit System StateI} `{HasLabel LabelI}
             `{HasInit System StateS} `{HasLabel LabelS}
             (ssI: Steps StateI LabelI) (ssS: Steps StateS LabelS)
             (impl spec: System) :=
    forall tr, Behavior ssI impl tr ->
               Behavior ssS spec tr.

End Behavior.

Notation "StI # StS |-- I <= S" := (Refines StI StS I S) (at level 30).
Notation "StI # StS |-- I ⊑ S" := (Refines StI StS I S) (at level 30).

(* Section BehaviorIO. *)

(*   Definition getInsLabel {LabelT} `{HasLabel LabelT} (l: LabelT): option Label := *)
(*     (getLabel l) >>=[None] *)
(*       (fun lbl => match lbl with *)
(*                   | LblIns _ => Some lbl *)
(*                   | _ => None *)
(*                   end). *)

(*   Definition getOutsLabel {LabelT} `{HasLabel LabelT} (l: LabelT): option Label := *)
(*     (getLabel l) >>=[None] *)
(*       (fun lbl => match lbl with *)
(*                   | LblOuts _ => Some lbl *)
(*                   | _ => None *)
(*                   end). *)

(*   Fixpoint behaviorInsOf {LabelT} `{HasLabel LabelT} (ll: list LabelT): Trace := *)
(*     match ll with *)
(*     | nil => nil *)
(*     | l :: ll' => (getInsLabel l) ::> (behaviorInsOf ll') *)
(*     end. *)

(*   Fixpoint behaviorOutsOf {LabelT} `{HasLabel LabelT} (ll: list LabelT): Trace := *)
(*     match ll with *)
(*     | nil => nil *)
(*     | l :: ll' => (getOutsLabel l) ::> (behaviorOutsOf ll') *)
(*     end. *)

(*   Definition behaviorIO {LabelT} `{HasLabel LabelT} (ll: list LabelT): Trace * Trace := *)
(*     (behaviorInsOf ll, behaviorOutsOf ll). *)
  
(*   Inductive BehaviorIO {StateT LabelT} *)
(*             `{HasInit System StateT} `{HasLabel LabelT} *)
(*             (ss: Steps StateT LabelT) : System -> Trace -> Trace -> Prop := *)
(*   | BehvIO: forall sys ll st, *)
(*       ss sys (initsOf sys) ll st -> *)
(*       forall trin trout, *)
(*         trin = behaviorInsOf ll -> *)
(*         trout = behaviorOutsOf ll -> *)
(*         BehaviorIO ss sys trin trout. *)

(*   Definition RefinesIO {StateI LabelI StateS LabelS} *)
(*              `{HasInit System StateI} `{HasLabel LabelI} *)
(*              `{HasInit System StateS} `{HasLabel LabelS} *)
(*              (ssI: Steps StateI LabelI) (ssS: Steps StateS LabelS) *)
(*              (impl spec: System) := *)
(*     forall trin trout, BehaviorIO ssI impl trin trout -> *)
(*                        BehaviorIO ssS spec trin trout. *)
  
(* End BehaviorIO. *)

(* Notation "StI # StS |-- I <~ S" := (RefinesIO StI StS I S) (at level 30). *)
(* Notation "StI # StS |-- I ≲ S" := (RefinesIO StI StS I S) (at level 30). *)

(** Some concrete state and label definitions *)

(* A basis state with [Msg]s. *)
Section BState.

  Record BState MsgT :=
    { bst_oss: OStates;
      bst_orqs: ORqs MsgT;
      bst_msgs: MessagePool MsgT
    }.

  Context {MsgT: Type} `{HasInit System (ORqs MsgT)}.

  Definition getBStateInit (sys: System): BState MsgT :=
    {| bst_oss := initsOf sys;
       bst_orqs := initsOf sys;
       bst_msgs := emptyMP _ |}.

  Global Instance BState_HasInit: HasInit System (BState MsgT) :=
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

Definition WfLbl (sys: System) (lbl: MLabel) :=
  match lbl with
  | RlblEmpty _ => True
  | RlblIns eins => eins <> nil /\ ValidMsgsExtIn sys eins
  | RlblOuts eouts => eouts <> nil /\ ValidMsgsExtOut sys eouts
  | RlblInt oidx ridx ins outs =>
    exists obj rule,
    In obj (sys_objs sys) /\ obj_idx obj = oidx /\
    In rule (obj_rules obj) /\ rule_idx rule = ridx /\
    ValidMsgsIn sys ins /\
    map msg_id (valsOf ins) = rule_msg_ids rule /\
    ValidMsgsOut sys outs /\
    DisjList (idsOf ins) (idsOf outs)
  end.

Definition WfHistory (sys: System) (hst: MHistory) :=
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

Section TState.

  Record TState :=
    { tst_oss: OStates;
      tst_orqs: ORqs TMsg;
      tst_msgs: MessagePool TMsg;
      tst_trss: MessagePool TMsg;
      tst_tid: TrsId
    }.

  Context `{HasInit System (ORqs TMsg)}.

  Definition getTStateInit (sys: System): TState :=
    {| tst_oss := initsOf sys;
       tst_orqs := initsOf sys;
       tst_msgs := emptyMP _;
       tst_trss := emptyMP _;
       tst_tid := trsIdInit |}.

  Global Instance TState_HasInit: HasInit System TState :=
    {| initsOf := getTStateInit |}.

End TState.

Close Scope list.

