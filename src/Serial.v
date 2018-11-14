Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT.
Require Import Topology.

Open Scope list.

(** [Atomic] and [Transactional] histories *)

Inductive TrsType :=
| TSlt | TIns | TOuts | TInt.

Section Sequential.
  Context {MsgT} `{HasMsg MsgT}.
  Context {oifc: OStateIfc}.

  Variables sys: System oifc.

  Hypothesis (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2}).

  Inductive Atomic:
    list (Id MsgT) (* initially-dequeued messages *) ->
    list (Id MsgT) (* all-dequeued  *) ->
    History MsgT (* history *) ->
    list (Id MsgT) (* all-enqueued *) ->
    list (Id MsgT) (* eventual outputs *) ->
    Prop :=
  | AtomicStart:
      forall oidx ridx ins outs,
        Atomic ins ins (RlblInt oidx ridx ins outs :: nil) outs outs
  | AtomicCont:
      forall inits ins hst outs eouts oidx ridx rins routs nins nouts neouts,
        Atomic inits ins hst outs eouts ->
        rins <> nil ->
        SubList rins eouts ->
        nins = ins ++ rins ->
        nouts = outs ++ routs ->
        neouts = removeL (id_dec msgT_dec) eouts rins ++ routs ->
        Atomic inits nins (RlblInt oidx ridx rins routs :: hst) nouts neouts.

  Definition AtomicEx (hst: History MsgT): Prop :=
    exists inits ins outs eouts,
      Atomic inits ins hst outs eouts.
  
  (* A history is [ExtAtomic] iff it is [Atomic] and starts from
   * a no or single external request.
   *)
  Inductive ExtAtomic: History MsgT -> Prop :=
  | ExtAtomicNil:
      forall ins hst outs eouts,
        Atomic nil ins hst outs eouts ->
        ExtAtomic hst
  | ExtAtomicSingle:
      forall rq ins hst outs eouts,
        In (idOf rq) (sys_merqs sys) ->
        Atomic [rq] ins hst outs eouts ->
        ExtAtomic hst.

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
      forall hst,
        ExtAtomic hst ->
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

Definition trsSteps {oifc} (sys: System oifc)
           (st1: MState oifc) (hst: MHistory) (st2: MState oifc) :=
  steps step_m sys st1 hst st2 /\
  Transactional sys msg_dec hst.

Definition seqSteps {oifc} (sys: System oifc)
           (st1: MState oifc) (hst: MHistory) (st2: MState oifc) :=
  steps step_m sys st1 hst st2 /\
  exists trss, Sequential sys msg_dec hst trss.

(* Definition BEquivalent (sys: System) *)
(*            {LabelT} `{HasLabel LabelT} (ll1 ll2: list LabelT) := *)
(*   behaviorOf ll1 = behaviorOf ll2. *)

(* Definition IOEquivalent (sys: System) *)
(*            {LabelT} `{HasLabel LabelT} (ll1 ll2: list LabelT) := *)
(*   behaviorIO ll1 = behaviorIO ll2. *)

Definition Serializable {oifc} (sys: System oifc) (ll: MHistory) (st: MState oifc) :=
  (* Legal and sequential *)
  exists sll, seqSteps sys (initsOf sys) sll st.

(* A system is serializable when all possible behaviors are [Serializable]. *)
Definition SerializableSys {oifc} (sys: System oifc) :=
  forall ll st,
    steps step_m sys (initsOf sys) ll st ->
    Serializable sys ll st.

Close Scope list.

