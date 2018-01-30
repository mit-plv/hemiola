Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepDet.

(** [Atomic] and [Transactional] histories *)

Section PerSystem.
  Variable sys: System.

  (* A history is [Atomic] if it satisfies the following conditions:
   * 0) The history can be either an incomplete or a complete transaction. 
   * 1) Each label in the history has a form of [IlblOuts (Some hdl) _],
   *    and all [hdl]s have the same [tinfo_tid]. It means that the history is
   *    for a single transaction.
   * 2) No external output messages are generated until the transaction ends.
   *    (Reflected in [AtomicCont])
   * 3) When the transaction ends, it outputs a single external message, which
   *    is the response of the original request.
   *    (Reflected in [AtomicFin])
   * 4) When the transaction ends, no internal messages about the transaction 
   *    are left. We ensure it by just tracking the internal messages about
   *    the transaction ([mouts]).
   *)
  Inductive Atomic: TInfo -> History -> MessagePool TMsg -> option TMsg -> Prop :=
  | AtomicImm:
      forall tid (rqin: Msg) rsout,
        isExternal sys (mid_from (msg_id rqin)) = true ->
        isExternal sys (mid_to (msg_id (tmsg_msg rsout))) = true ->
        Atomic (buildTInfo tid rqin)
               (IlblOuts (Some (toTMsgU rqin)) (rsout :: nil) :: nil)
               nil (Some rsout)
  | AtomicStart:
      forall tid (rqin: Msg) houts,
        isExternal sys (mid_from (msg_id rqin)) = true ->
        ForallMP (fun tmsg => isInternal sys (mid_to (msg_id (tmsg_msg tmsg))) = true /\
                              tmsg_info tmsg = Some (buildTInfo tid rqin)) houts ->
        Atomic (buildTInfo tid rqin)
               (IlblOuts (Some (toTMsgU rqin)) houts :: nil) houts None
  | AtomicCont:
      forall ti hst mouts hdl houts,
        Atomic ti hst mouts None ->
        isInternal sys (mid_from (msg_id (tmsg_msg hdl))) = true ->
        In hdl mouts ->
        ForallMP (fun tmsg => isInternal sys (mid_to (msg_id (tmsg_msg tmsg))) = true) houts ->
        Atomic ti (IlblOuts (Some hdl) houts :: hst)
               (distributeMsgs houts (removeOnce tmsg_dec hdl mouts)) None
  | AtomicFin:
      forall ti hst hdl rsout,
        Atomic ti hst (hdl :: nil) None ->
        isInternal sys (mid_from (msg_id (tmsg_msg hdl))) = true ->
        isExternal sys (mid_to (msg_id (tmsg_msg rsout))) = true ->
        Atomic ti (IlblOuts (Some hdl) (rsout :: nil) :: hst)
               nil (Some rsout).

  Inductive Transactional: History -> Prop :=
  | TrsSlt:
      Transactional (emptyILabel :: nil)
  | TrsIn:
      forall msg tin,
        tin = IlblIn msg ->
        Transactional (tin :: nil)
  | TrsAtomic:
      forall ti hst mouts orsout,
        Atomic ti hst mouts orsout ->
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

