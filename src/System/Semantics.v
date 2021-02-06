Require Import Bool List String PeanoNat.
Require Import Common FMap Syntax.

Require Export MessagePool.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Definition extRqsOf `{DecValue} `{OStateIfc}
           (sys: System) (mp: MessagePool Msg) :=
  qsOf (sys_merqs sys) mp.

Definition extRssOf `{DecValue} `{OStateIfc}
           (sys: System) (mp: MessagePool Msg) :=
  qsOf (sys_merss sys) mp.

Section Validness.
  Context `{DecValue} `{OStateIfc}.

  (* A set of messages are "well-distributed" iff the sources of
   * all messages are different from each others.
   *)
  Definition WellDistrMsgs (msgs: list (Id Msg)) :=
    NoDup (idsOf msgs).

  (* A set of messages are "valid internal inputs" iff
   * 1) each source is internal and
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsIn (sys: System) (msgs: list (Id Msg)) :=
    SubList (idsOf msgs) (sys_minds sys ++ sys_merqs sys) /\
    WellDistrMsgs msgs.

  (* A set of messages are "valid outputs" iff
   * 1) each message is using either an internal or
   *    an external-response queue.
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsOut (sys: System) (msgs: list (Id Msg)) :=
    SubList (idsOf msgs) (sys_minds sys ++ sys_merss sys) /\
    WellDistrMsgs msgs.

  (* A set of messages are "valid external inputs" iff
   * 1) each message uses an external request queue and
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsExtIn (sys: System) (msgs: list (Id Msg)) :=
    SubList (idsOf msgs) (sys_merqs sys) /\
    WellDistrMsgs msgs.

  (* A set of messages are "valid external outputs" iff
   * 1) each message uses an external response queue and
   * 2) they are well-distributed.
   *)
  Definition ValidMsgsExtOut (sys: System) (msgs: list (Id Msg)) :=
    SubList (idsOf msgs) (sys_merss sys) /\
    WellDistrMsgs msgs.

End Validness.

Section HasLabel.
  Context `{DecValue}.

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

  Section Labeled.
    Context {LabelT} `{HasLabel LabelT}.

    Definition Trace := list Label.

    Definition Reachable {SystemT StateT} `{HasInit SystemT StateT}
               (ss: Steps SystemT StateT LabelT) (sys: SystemT) (st: StateT): Prop :=
      exists ll, ss sys (initsOf sys) ll st.

    Fixpoint behaviorOf  (ll: list LabelT): Trace :=
      match ll with
      | nil => nil
      | l :: ll' => (getLabel l) ::> (behaviorOf ll')
      end.

    Inductive Behavior {SystemT StateT} `{HasInit SystemT StateT}
              (ss: Steps SystemT StateT LabelT) : SystemT -> Trace -> Prop :=
    | Behv: forall sys ll st,
        ss sys (initsOf sys) ll st ->
        forall tr,
          tr = behaviorOf ll ->
          Behavior ss sys tr.

  End Labeled.

  Definition Refines `{dv: DecValue} {SystemI StateI LabelI SystemS StateS LabelS}
             `{HasInit SystemI StateI} `{HasInit SystemS StateS}
             `{@HasLabel dv LabelI} `{@HasLabel dv LabelS}
             (ssI: Steps SystemI StateI LabelI) (ssS: Steps SystemS StateS LabelS)
             (impl: SystemI) (spec: SystemS) :=
    forall tr, Behavior ssI impl tr ->
               Behavior ssS spec tr.

End Behavior.

Notation "StI # StS |-- I <= S" := (Refines StI StS I S) (at level 30).
Notation "StI # StS |-- I ⊑ S" := (Refines StI StS I S) (at level 30).

(** Some concrete state and label definitions *)

Record State `{DecValue} `{OStateIfc} :=
  { st_oss: OStates;
    st_orqs: ORqs Msg;
    st_msgs: MessagePool Msg
  }.

Definition getStateInit `{DecValue} `{OStateIfc} (sys: System): State :=
  {| st_oss := initsOf sys;
     st_orqs := initsOf sys;
     st_msgs := emptyMP _ |}.

Global Instance State_HasInit `{DecValue} `{OStateIfc}: HasInit System State :=
  {| initsOf := getStateInit |}.

Definition GoodORqsInit `{DecValue} (iorqs: ORqs Msg): Prop :=
  forall oidx,
    iorqs@[oidx] >>=[True] (fun orq => orq = []).

Definition IntMsgsEmpty `{DecValue} `{OStateIfc}
           (sys: System) (msgs: MessagePool Msg) :=
  forall midx,
    In midx sys.(sys_minds) ->
    findQ midx msgs = nil.

(* [RLabel] represents "internal rule-driven labels" that reveal which message
 * is being handled now.
 *)
Section RLabel.
  Context `{DecValue}.

  Inductive RLabel :=
  | RlblEmpty
  | RlblIns (mins: list (Id Msg)): RLabel
  | RlblInt (oidx ridx: IdxT) (mins: list (Id Msg)) (mouts: list (Id Msg)): RLabel
  | RlblOuts (mouts: list (Id Msg)): RLabel.

  Definition rToLabel (l: RLabel): option Label :=
    match l with
    | RlblEmpty => None
    | RlblIns mins => Some (LblIns mins)
    | RlblInt _ _ _ _ => None
    | RlblOuts mouts => Some (LblOuts mouts)
    end.

  Global Instance RLabel_HasLabel: HasLabel RLabel :=
    { getLabel := rToLabel }.

End RLabel.

Definition History `{DecValue} := list RLabel.
