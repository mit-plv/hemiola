Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT.
Require Import Topology.

(** [Atomic] and [Transactional] histories *)

Inductive TrsType :=
| TSlt | TIns | TOuts | TInt.

Section Sequential.
  Variable sys: System.

  Context {MsgT} `{HasMsg MsgT}.
  Hypothesis (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2}).

  (** NOTE: head is the oldest *)
  Inductive Atomic:
    list (Id MsgT) (* initially-dequeued messages *) ->
    list (Id MsgT) (* all-dequeued  *) ->
    History MsgT (* history *) ->
    list (Id MsgT) (* all-enqueued *) ->
    list (Id MsgT) (* eventual outputs *) ->
    Prop :=
  | AtomicStart:
      forall rule ins outs,
        Atomic ins ins (RlblInt rule ins outs :: nil) outs outs
  | AtomicCont:
      forall inits ins hst outs eouts rule rins routs nins nouts neouts,
        Atomic inits ins hst outs eouts ->
        rins <> nil ->
        SubList rins eouts ->
        nins = ins ++ rins ->
        nouts = outs ++ routs ->
        neouts = removeL (id_dec msgT_dec) eouts rins ++ routs ->
        Atomic inits nins (RlblInt rule rins routs :: hst) nouts neouts.

  (* A history is [ExtAtomic] iff it is [Atomic] and starts from
   * a single external request.
   *)
  Inductive ExtAtomic: Id MsgT -> History MsgT -> Prop :=
  | ExtAtomicIntro:
      forall rq ins hst outs eouts,
        In (idOf rq) (merqsOf sys) ->
        Atomic [rq] ins hst outs eouts ->
        ExtAtomic rq hst.

  Inductive Transactional: History MsgT -> Prop :=
  | TrsSlt:
      Transactional (RlblEmpty _ :: nil)
  | TrsIns:
      forall eins tin,
        tin = RlblIns eins ->
        Transactional (tin :: nil)
  | TrsOuts:
      forall eouts tout,
        tout = RlblOuts eouts ->
        Transactional (tout :: nil)
  | TrsAtomic:
      forall rq hst,
        ExtAtomic rq hst ->
        Transactional hst.

  Definition Sequential (hst: History MsgT) (trss: list (History MsgT)) :=
    Forall Transactional trss /\ hst = List.concat trss.

End Sequential.

Section Semi.
  Context {MsgT} `{HasMsg MsgT}.
  Hypothesis (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2}).

  Inductive STransactional: History MsgT -> Prop :=
  | STrsSlt:
      STransactional (RlblEmpty _ :: nil)
  | STrsIns:
      forall eins tin,
        tin = RlblIns eins ->
        STransactional (tin :: nil)
  | STrsOuts:
      forall eouts tout,
        tout = RlblOuts eouts ->
        STransactional (tout :: nil)
  | STrsAtomic:
      forall inits ins hst outs eouts,
        Atomic msgT_dec inits ins hst outs eouts ->
        STransactional hst.

  Inductive SSequential: History MsgT -> nat -> Prop :=
  | SSeqIntro:
      forall trss hst lth,
        hst = List.concat trss ->
        lth = List.length trss ->
        Forall STransactional trss ->
        SSequential hst lth.

End Semi.

(*! Serializability *)

Definition trsSteps {StateT MsgT} `{HasMsg MsgT}
           (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2})
           (step: Step System StateT (RLabel MsgT))
           (sys: System) (st1: StateT) (hst: History MsgT) (st2: StateT) :=
  steps step sys st1 hst st2 /\
  Transactional sys msgT_dec hst.

Definition trsStepsM := trsSteps msg_dec step_m.
Definition trsStepsT := trsSteps tmsg_dec step_t.

Definition seqSteps {StateT MsgT} `{HasMsg MsgT}
           (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2})
           (step: Step System StateT (RLabel MsgT))
           (sys: System) (st1: StateT) (hst: History MsgT) (st2: StateT) :=
  steps step sys st1 hst st2 /\
  exists trss, Sequential sys msgT_dec hst trss.

Definition seqStepsM := seqSteps msg_dec step_m.
Definition seqStepsT := seqSteps tmsg_dec step_t.

Definition BEquivalent (sys: System)
           {LabelT} `{HasLabel LabelT} (ll1 ll2: list LabelT) :=
  behaviorOf sys ll1 = behaviorOf sys ll2.

Definition Serializable (sys: System) (ll: MHistory) :=
  exists sll sst,
    (* 1) legal, 2) sequential, and *) seqStepsM sys (initsOf sys) sll sst /\
    (* 3) behavior-equivalent *) BEquivalent sys ll sll.

(* A system is serializable when all possible behaviors are [Serializable]. *)
Definition SerializableSys (sys: System) :=
  forall ll st,
    steps step_m sys (initsOf sys) ll st ->
    Serializable sys ll.

