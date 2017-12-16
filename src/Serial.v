Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet.

Section PerSystem.
  Variable sys: System.
  Variable step: Step MState MLabel.

  Definition History := list MLabel.

  (* Note that due to the definition of [Msg], it is guaranteed that
   * an [Atomic] history is about a single transaction.
   * [Msg] contains [tmsg_tid], and [In hdl mouts] in [AtomicCons]
   * ensures that the history is for a single transaction.
   *)
  Inductive Atomic: Msg -> History -> list Msg -> Prop :=
  | AtomicBase:
      forall hdl,
        isExternal sys (mid_from (msg_id hdl)) = true ->
        Atomic hdl nil (hdl :: nil)
  | AtomicCons:
      forall min hst mouts,
        Atomic min hst mouts ->
        forall hdl houts,
          In hdl mouts ->
          Atomic min (IlblOuts (Some hdl) houts :: hst)
                 (List.remove msg_dec hdl mouts ++ houts).

  Inductive Transactional: History -> Prop :=
  | TrsSlt:
      Transactional (emptyILabel :: nil)
  | TrsIn:
      forall msg tin,
        tin = IlblIn msg ->
        Transactional (tin :: nil)
  | TrsAtomic:
      forall min hst mouts,
        Atomic min hst mouts ->
        Transactional hst.

  Definition Sequential (hst: History) :=
    exists trss: list History,
      Forall Transactional trss /\
      hst = concat trss.

End PerSystem.

Definition trsSteps (sys: System) (st1: MState) (hst: History) (st2: MState) :=
  steps_det sys st1 hst st2 /\
  Transactional sys hst.

Definition seqSteps (sys: System) (st1: MState) (hst: History) (st2: MState) :=
  steps_det sys st1 hst st2 /\
  Sequential sys hst.

Definition Equivalent (sys: System)
           {LabelT} `{HasLabel LabelT} (ll1 ll2: list LabelT) :=
  behaviorOf sys ll1 = behaviorOf sys ll2.

Definition Serializable (sys: System) (ll: History) :=
  exists sll sst,
    (* 1) legal and sequential *) seqSteps sys (getStateInit sys) sll sst /\
    (* 3) equivalent *) Equivalent sys ll sll.

(* A system is serializable when all possible behaviors are [Serializable]. *)
Definition SerializableSys (sys: System) :=
  forall ll st,
    steps_det sys (getStateInit sys) ll st ->
    Serializable sys ll.

