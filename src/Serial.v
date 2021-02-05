Require Import Bool List String PeanoNat.
Require Import Common ListSupport FMap Syntax Semantics StepM.
Require Import Topology.

Local Open Scope list.

(** [Atomic] and [Transactional] histories *)

Section Sequential.
  Context `{DecValue} `{OStateIfc}.
  Variables sys: System.

  Inductive Atomic:
    list (Id Msg) (* initially-dequeued messages *) ->
    list (Id Msg) (* all-dequeued *) ->
    History (* history *) ->
    list (Id Msg) (* all-enqueued *) ->
    list (Id Msg) (* eventual outputs *) ->
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
        neouts = removeL (id_dec msg_dec) eouts rins ++ routs ->
        Atomic inits nins (RlblInt oidx ridx rins routs :: hst) nouts neouts.

  Definition AtomicEx (hst: History): Prop :=
    exists inits ins outs eouts,
      Atomic inits ins hst outs eouts.

  (* A history is [ExtAtomic] iff it is [Atomic] and starts from some
   * external requests (possibly [nil])
   *)
  Inductive ExtAtomic: list (Id Msg) -> History -> list (Id Msg) -> Prop :=
  | ExtAtomicIntro:
      forall rqs ins hst outs eouts,
        SubList (idsOf rqs) (sys_merqs sys) ->
        Atomic rqs ins hst outs eouts ->
        ExtAtomic rqs hst eouts.

  (* A history is [IntAtomic] iff it is [Atomic] and starts from some
   * non-external requests. Note that initial messages cannot be [nil].
   *)
  Inductive IntAtomic: History -> list (Id Msg) -> Prop :=
  | IntAtomicIntro:
      forall inits ins hst outs eouts,
        ~ SubList (idsOf inits) (sys_merqs sys) ->
        Atomic inits ins hst outs eouts ->
        IntAtomic hst eouts.

  Inductive Transactional: History -> Prop :=
  | TrsSlt:
      Transactional (RlblEmpty :: nil)
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

  Definition Sequential (hst: History) (trss: list History) :=
    Forall Transactional trss /\ hst = List.concat trss.

End Sequential.

Section Semi.
  Context `{DecValue} `{OStateIfc}.
  Variables sys: System.

  Inductive STransactional: History -> nat -> Prop :=
  | STrsSlt:
      STransactional (RlblEmpty :: nil) 0
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
        IntAtomic sys hst eouts ->
        STransactional hst (List.length hst)
  | STrsExtAtomic:
      forall inits hst eouts,
        ExtAtomic sys inits hst eouts ->
        STransactional hst 0.

  Inductive SSequential: list History -> nat -> Prop :=
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

Definition trsSteps `{DecValue} `{OStateIfc} (sys: System)
           (st1: State) (hst: History) (st2: State) :=
  steps step_m sys st1 hst st2 /\
  Transactional sys hst.

Definition seqSteps `{DecValue} `{OStateIfc} (sys: System)
           (st1: State) (hst: History) (st2: State) :=
  steps step_m sys st1 hst st2 /\
  exists trss, Sequential sys hst trss.

Definition Serializable `{DecValue} `{OStateIfc} (sys: System) (st: State) :=
  (* Legal and sequential *)
  exists sll, seqSteps sys (initsOf sys) sll st.

(* A system is serializable when all possible behaviors are [Serializable]. *)
Definition SerializableSys `{DecValue} `{OStateIfc} (sys: System) :=
  forall st,
    Reachable (steps step_m) sys st ->
    Serializable sys st.
