Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepDet.

(** [Atomic] and [Transactional] histories *)

Section PerSystem.
  Variable sys: System.

  (* A history is [Atomic] if it satisfies following conditions:
   * 1) The history can be either an incomplete or a complete transaction.
   * 2) The history always begins by handling an external message.
   * 3) Each label in the history has a form of [IlblOuts (Some hdl) _],
   *    and all [hdl]s have the same [tinfo_tid]. It means that the history is
   *    for a single transaction.
   *)
  Inductive Atomic: TrsId -> Msg -> History -> MessagePool TMsg -> Prop :=
  | AtomicStart:
      forall ts rqr rq houts,
        isExternal sys (mid_from (msg_id rq)) = true ->
        ForallMP (fun tmsg => tmsg_info tmsg =
                              Some (buildTInfo ts (rq :: nil))) houts ->
        Atomic ts rq (IlblOuts (Some rqr) (toTMsgU rq :: nil) houts :: nil) houts
  | AtomicCont:
      forall ts rq hst rule msgs mouts houts,
        Atomic ts rq hst mouts ->
        msgs <> nil ->
        SubList msgs mouts ->
        Atomic ts rq (IlblOuts (Some rule) msgs houts :: hst)
               (distributeMsgs houts (removeMsgs msgs mouts)).

  Inductive Transactional: History -> Prop :=
  | TrsSlt:
      Transactional (emptyILabel :: nil)
  | TrsIn:
      forall msg tin,
        tin = IlblIn msg ->
        Transactional (tin :: nil)
  | TrsAtomic:
      forall ts rq hst mouts,
        Atomic ts rq hst mouts ->
        Transactional hst.

  Definition Sequential (hst: History) :=
    exists trss: list History,
      Forall Transactional trss /\
      hst = concat trss.

End PerSystem.

(** Transaction messages in [MessagePool] *)

Definition trsMessages (trsInfo: TInfo) (mp: MessagePool TMsg) : list TMsg :=
  filter (fun tmsg =>
            match tmsg_info tmsg with
            | Some tinfo => if tinfo_dec tinfo trsInfo then true else false
            | None => false
            end) mp.

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

