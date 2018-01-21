Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepDet.

(** [Atomic] and [Transactional] histories *)

Section PerSystem.
  Variable sys: System.

  (* Note that due to the definition of [TMsg], it is guaranteed that an
   * [Atomic] history is about a single transaction. [TMsg] contains
   * [tmsg_tid], and [In hdl mouts] in [AtomicCons] ensures that the history is
   * for a single transaction.
   *)
  Inductive Atomic: TMsg -> History -> list TMsg -> option TMsg -> Prop :=
  | AtomicBase:
      forall hdl,
        isExternal sys (mid_from (msg_id (getMsg hdl))) = true ->
        Atomic hdl nil (hdl :: nil) None
  | AtomicCont:
      forall rqin hst mouts,
        Atomic rqin hst mouts None ->
        forall hdl houts,
          In hdl mouts ->
          Forall (fun tmsg => isInternal sys (mid_to (msg_id (tmsg_msg tmsg)))
                              = true) houts ->
          Atomic rqin (IlblOuts (Some hdl) houts :: hst)
                 (List.remove tmsg_dec hdl mouts ++ houts) None
  | AtomicFin:
      forall rqin hst hdl rsout,
        Atomic rqin hst (hdl :: nil) None ->
        isExternal sys (mid_to (msg_id (tmsg_msg rsout))) = true ->
        Atomic rqin (IlblOuts (Some hdl) (rsout :: nil) :: hst)
               nil (Some rsout).

  Inductive Transactional: History -> Prop :=
  | TrsSlt:
      Transactional (emptyILabel :: nil)
  | TrsIn:
      forall msg tin,
        tin = IlblIn msg ->
        Transactional (tin :: nil)
  | TrsAtomic:
      forall rqin hst mouts orsout,
        Atomic rqin hst mouts orsout ->
        hst <> nil ->
        Transactional hst.

  Definition Sequential (hst: History) :=
    exists trss: list History,
      Forall Transactional trss /\
      hst = concat trss.

End PerSystem.

(** Serializability *)

Definition trsSteps (sys: System) (st1: TState) (hst: History) (st2: TState) :=
  steps_det sys st1 hst st2 /\
  Transactional sys hst.

Definition seqSteps (sys: System) (st1: TState) (hst: History) (st2: TState) :=
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

