Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepM StepT.
Require Import Topology.

(** [Atomic] and [Transactional] histories *)

Section PerSystem.
  Variable sys: System.

  Context {MsgT} `{HasMsg MsgT}.

  (* A history is [Atomic] if it satisfies following conditions:
   * 1) The history can be either an incomplete or a complete transaction.
   * 2) Each label in the history has a form of [RlblOuts (Some hdl) _],
   *    and all [hdl]s have the same [tinfo_tid]. It means that the history is
   *    for a single transaction.
   *)
  Inductive Atomic: Id MsgT -> History MsgT -> MessagePool MsgT -> Prop :=
  | AtomicStart:
      forall rqr rq houts,
        Atomic rq (RlblInt (Some rqr) (rq :: nil) houts :: nil)
               (enqMsgs houts (emptyMP _))
  | AtomicCont:
      forall rq hst rule msgs mouts houts,
        Atomic rq hst mouts ->
        msgs <> nil ->
        Forall (fun idm => InMP (idOf idm) (valOf idm) mouts) msgs ->
        Atomic rq (RlblInt (Some rule) msgs houts :: hst)
               (enqMsgs houts (deqMsgs (idsOf msgs) mouts)).

  (* A history is [ExtAtomic] iff it is [Atomic] and starts from
   * an external request.
   *)
  Inductive ExtAtomic: Id MsgT -> History MsgT -> MessagePool MsgT -> Prop :=
  | ExtAtomicIntro:
      forall rq hst mouts,
        In (idOf rq) (merqsOf sys) ->
        Atomic rq hst mouts ->
        ExtAtomic rq hst mouts.

  Inductive Transactional: History MsgT -> Prop :=
  | TrsSlt:
      Transactional (emptyRLabel _ :: nil)
  | TrsIns:
      forall eins tin,
        tin = RlblIns eins ->
        Transactional (tin :: nil)
  | TrsOuts:
      forall eouts tout,
        tout = RlblOuts eouts ->
        Transactional (tout :: nil)
  | TrsAtomic:
      forall rq hst mouts,
        ExtAtomic rq hst mouts ->
        Transactional hst.

  Definition Sequential (hst: History MsgT) :=
    exists trss: list (History MsgT),
      Forall Transactional trss /\
      hst = List.concat trss.

End PerSystem.

(*! Serializability *)

Definition trsSteps {StateT MsgT} `{HasMsg MsgT}
           (step: Step System StateT (RLabel MsgT))
           (sys: System) (st1: StateT) (hst: History MsgT) (st2: StateT) :=
  steps step sys st1 hst st2 /\
  Transactional sys hst.

Definition trsStepsM := trsSteps step_m.
Definition trsStepsT := trsSteps step_t.

Definition seqSteps {StateT MsgT} `{HasMsg MsgT}
           (step: Step System StateT (RLabel MsgT))
           (sys: System) (st1: StateT) (hst: History MsgT) (st2: StateT) :=
  steps step sys st1 hst st2 /\
  Sequential sys hst.

Definition seqStepsM := seqSteps step_m.
Definition seqStepsT := seqSteps step_t.

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

(** Some static conditions that ensure [SerializableSys]. *)

Fixpoint getDownRq (topo: CTree) (oidx: IdxT) (orq: ORq Msg) :=
  match orq with
  | nil => None
  | ri :: orq' =>
    if isFromParent topo oidx (rqh_from ri) then
      Some ri
    else getDownRq topo oidx orq'
  end.

Fixpoint getUpRq (topo: CTree) (oidx: IdxT) (orq: ORq Msg) :=
  match orq with
  | nil => None
  | ri :: orq' =>
    if isFromChild topo oidx (rqh_from ri) then
      Some ri
    else getUpRq topo oidx orq'
  end.

(* TODO: need a more intuitive (easier) definition. *)
Definition PartialBlockingPrec (topo: CTree) (oidx: IdxT): RPrecond :=
  fun (ost: OState) (orq: ORq Msg) (ins: list (Id Msg)) =>
    match getDownRq topo oidx orq with
    | Some dri =>
      Forall (fun msg => msg_id msg = msg_id (rqh_msg dri) /\
                         msg_rr msg = Rs) (valsOf ins) /\
      rqh_fwds dri = idsOf ins
    | None =>
      match getUpRq topo oidx orq with
      | Some uri => 
        SubList (idsOf ins) (chnsFromParent topo oidx) /\
        Forall (fun msg => msg_id msg = msg_id (rqh_msg uri) /\
                           msg_rr msg = Rs) (valsOf ins)
      | None => True
      end
    end.

Definition PartialBlockingRule (topo: CTree) (rule: Rule) :=
  (rule_precond rule)
  ->rprec (PartialBlockingPrec topo (rule_oidx rule)).

Definition PartialBlockingSys (topo: CTree) (sys: System) :=
  Forall (PartialBlockingRule topo) (sys_rules sys).

