Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM.
Require Import Topology.

Open Scope list.

(** [Atomic] and [Transactional] histories *)

Section Sequential.
  Context {oifc: OStateIfc}.
  Variables sys: System oifc.

  Context {MsgT} `{HasMsg MsgT}.
  Hypothesis (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2}).

  Inductive Atomic:
    list (Id MsgT) (* initially-dequeued messages *) ->
    list (Id MsgT) (* all-dequeued *) ->
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

  (* A history is [ExtAtomic] iff it is [Atomic] and starts from some
   * external requests (possibly [nil]) 
   *)
  Inductive ExtAtomic: list (Id MsgT) -> History MsgT -> list (Id MsgT) -> Prop :=
  | ExtAtomicIntro:
      forall rqs ins hst outs eouts,
        SubList (idsOf rqs) (sys_merqs sys) ->
        Atomic rqs ins hst outs eouts ->
        ExtAtomic rqs hst eouts.

  Inductive IntAtomic: History MsgT -> list (Id MsgT) -> Prop :=
  | IntAtomicIntro:
      forall inits ins hst outs eouts,
        ~ SubList (idsOf inits) (sys_merqs sys) ->
        Atomic inits ins hst outs eouts ->
        IntAtomic hst eouts.

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
      forall inits hst eouts,
        ExtAtomic inits hst eouts ->
        Transactional hst.

  Definition Sequential (hst: History MsgT) (trss: list (History MsgT)) :=
    Forall Transactional trss /\ hst = List.concat trss.

End Sequential.

Section Semi.
  Context {oifc: OStateIfc}.
  Variables sys: System oifc.

  Context {MsgT} `{HasMsg MsgT}.
  Hypothesis (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2}).

  Inductive STransactional: History MsgT -> nat -> Prop :=
  | STrsSlt:
      STransactional (RlblEmpty _ :: nil) 0
  | STrsIns:
      forall eins tin,
        tin = RlblIns eins ->
        STransactional (tin :: nil) 0
  | STrsOuts:
      forall eouts tout,
        tout = RlblOuts eouts ->
        STransactional (tout :: nil) 0
  | STrsIntAtomic:
      forall hst eouts,
        IntAtomic sys msgT_dec hst eouts ->
        STransactional hst (List.length hst)
  | STrsExtAtomic:
      forall inits hst eouts,
        ExtAtomic sys msgT_dec inits hst eouts ->
        STransactional hst 0.

  Inductive SSequential: list (History MsgT) -> nat -> Prop :=
  | SSeqNil: SSequential nil 0
  | SSeqConcat:
      forall trss n trs tn ntrss nn,
        SSequential trss n ->
        STransactional trs tn ->
        ntrss = trs :: trss ->
        nn = tn + n ->
        SSequential ntrss nn.

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

Definition Serializable {oifc} (sys: System oifc) (ll: MHistory) (st: MState oifc) :=
  (* Legal and sequential *)
  exists sll, seqSteps sys (initsOf sys) sll st.

(* A system is serializable when all possible behaviors are [Serializable]. *)
Definition SerializableSys {oifc} (sys: System oifc) :=
  forall ll st,
    steps step_m sys (initsOf sys) ll st ->
    Serializable sys ll st.

Close Scope list.

