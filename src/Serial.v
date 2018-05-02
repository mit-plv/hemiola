Require Import Bool List String Peano_dec.
Require Import Common ListSupport FMap Syntax Semantics StepT.

(** [Atomic] and [Transactional] histories *)

Section PerSystem.
  Variable sys: System.

  (* A history is [Atomic] if it satisfies following conditions:
   * 1) The history can be either an incomplete or a complete transaction.
   * 2) The history always begins by handling an external message.
   * 3) Each label in the history has a form of [RlblOuts (Some hdl) _],
   *    and all [hdl]s have the same [tinfo_tid]. It means that the history is
   *    for a single transaction.
   *)
  Inductive Atomic: TrsId -> Id Msg -> THistory -> MessagePool TMsg -> Prop :=
  | AtomicStart:
      forall ts rqr rq houts,
        In (idOf rq) (merqsOf sys) ->
        Forall (fun idm => tmsg_info (valOf idm) =
                           Some (buildTInfo ts (rq :: nil))) houts ->
        Atomic ts rq (RlblInt (Some rqr) (liftI toTMsgU rq :: nil) houts :: nil)
               (enqMsgs houts (emptyMP _))
  | AtomicCont:
      forall ts rq hst rule msgs mouts houts,
        Atomic ts rq hst mouts ->
        msgs <> nil ->
        Forall (fun idm => InMP (idOf idm) (valOf idm) mouts) msgs ->
        Atomic ts rq (RlblInt (Some rule) msgs houts :: hst)
               (enqMsgs houts (deqMsgs (idsOf msgs) mouts)).

  Inductive Transactional: THistory -> Prop :=
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
      forall ts rq hst mouts,
        Atomic ts rq hst mouts ->
        Transactional hst.

  Definition Sequential (hst: THistory) :=
    exists trss: list THistory,
      Forall Transactional trss /\
      hst = List.concat trss.

End PerSystem.

(** Serializability *)

Definition trsSteps (sys: System) (st1: TState) (hst: THistory) (st2: TState) :=
  steps step_t sys st1 hst st2 /\
  Transactional sys hst.

Definition seqSteps (sys: System) (st1: TState) (hst: THistory) (st2: TState) :=
  steps step_t sys st1 hst st2 /\
  Sequential sys hst.

Definition BEquivalent (sys: System)
           {LabelT} `{HasLabel LabelT} (ll1 ll2: list LabelT) :=
  behaviorOf sys ll1 = behaviorOf sys ll2.

Definition Serializable (sys: System) (ll: THistory) :=
  exists sll sst,
    (* 1) legal, 2) sequential, and *) seqSteps sys (initsOf sys) sll sst /\
    (* 3) behavior-equivalent *) BEquivalent sys ll sll.

(* A system is serializable when all possible behaviors are [Serializable]. *)
Definition SerializableSys (sys: System) :=
  forall ll st,
    steps step_t sys (initsOf sys) ll st ->
    Serializable sys ll.

(** Let's start (experimentally) with an obvious condition 
 * that ensures [SerializableSys] 
 *)

(* Definition TotallyBlockingPrec: RPrecond := *)
(*   fun ost orq ins => *)
(*     SubList (map (fun msg => mid_tid (msg_id msg)) ins) *)
(*             (map (fun msg => mid_tid (msg_id msg)) orq). *)

(* Definition TotallyBlockingRule (rule: Rule) := *)
(*   (rule_precond rule) ->rprec TotallyBlockingPrec. *)

(* Definition TotallyBlockingSys (sys: System) := *)
(*   Forall TotallyBlockingRule (sys_rules sys). *)

(* Theorem TotallyBlockingSys_SerializableSys: *)
(*   forall sys, TotallyBlockingSys sys -> SerializableSys sys. *)
(* Proof. *)
(*   unfold SerializableSys, Serializable; intros. *)
(*   eexists; exists st; split; [split|]. *)
  
