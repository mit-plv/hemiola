Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics.

Section PerSystem.
  Variable sys: System.
  Variable step: Step Msg.

  Record HLabel :=
    { hlbl_hdl : Msg;
      hlbl_outs : list Msg
    }.

  Definition toHLabel (l: Label): option HLabel :=
    match l with
    | LblHdl hdl outs => Some {| hlbl_hdl := hdl; hlbl_outs := outs |}
    | _ => None
    end.

  Definition History := list HLabel.

  Fixpoint historyOf (ll: list Label): History :=
    match ll with
    | nil => nil
    | lbl :: ll' => (toHLabel lbl) ::> (historyOf ll')
    end.

  Inductive HistoryOf: History -> Prop :=
  | Hist: forall ll st,
      steps step sys (getStateInit sys) ll st ->
      HistoryOf (historyOf ll).

  Inductive Atomic: Msg -> History -> list Msg -> Prop :=
  | AtomicBase:
      forall min hlbl mouts,
        hlbl = {| hlbl_hdl := min; hlbl_outs := mouts |} ->
        Atomic min (hlbl :: nil) mouts
  | AtomicCons:
      forall min hst mouts,
        Atomic min hst mouts ->
        forall hdl houts,
          In hdl mouts ->
          Atomic min ({| hlbl_hdl := hdl; hlbl_outs := houts |} :: hst)
                 (List.remove msg_dec hdl mouts ++ houts).

  (* Definition isTrsPair (rq rs: MsgId) := *)
  (*   (if mid_from rq ==n mid_to rs then true else false) *)
  (*     && (if mid_to rq ==n mid_from rs then true else false) *)
  (*     && (if mid_type rq ==n mid_type rs then true else false). *)

  (* Definition AtomicTrs (hst: History) := *)
  (*   exists min mout, *)
  (*     isExternal sys (mid_from (msg_id min)) = true /\ *)
  (*     isTrsPair (msg_id min) (msg_id mout) = true /\ *)
  (*     Atomic min hst (mout :: nil). *)

  (* Definition IncompleteTrs (hst: History) := *)
  (*   exists min mouts, *)
  (*     isExternal sys (mid_from (msg_id min)) = true /\ *)
  (*     Forall (fun m => isInternal sys (mid_to (msg_id m)) = true) mouts /\ *)
  (*     Atomic min hst mouts. *)

  (* Definition Transactional (hst: History) := *)
  (*   AtomicTrs hst \/ IncompleteTrs hst. *)

  Definition Transactional (hst: History) :=
    hst = nil \/
    (exists min mouts,
        isExternal sys (mid_from (msg_id min)) = true /\
        Atomic min hst mouts).

  Definition Sequential (hst: History) :=
    exists (trs: list History),
      Forall Transactional trs /\ hst = concat trs.

End PerSystem.

Definition insOf (obj: Object) (hst: History) :=
  filter (fun hl =>
            if obj_idx obj ==n mid_from (msg_id (hlbl_hdl hl))
            then true else false) hst.

(* Two histories are equivalent if
 * 1) one history is a permutation of the other, and
 * 2) they have the same in-orders per an object.
 *)
Definition Equivalent (hst1 hst2: History) :=
  Permutation hst1 hst2 /\
  forall obj, insOf obj hst1 = insOf obj hst2.

Infix "≡" := Equivalent (at level 30).

Definition Serializable (sys: System) (step: Step Msg) (ll: list Label) :=
  exists sll sst,
    steps step sys (getStateInit sys) sll sst /\
    Sequential sys (historyOf sll) /\
    (* behaviorOf ll = behaviorOf sll /\ *)
    Equivalent (historyOf ll) (historyOf sll).

(* A system is [Serial] when all possible behaviors are [Serializable]. *)
Definition Serial (sys: System) (step: Step Msg) :=
  forall ll st,
    steps step sys (getStateInit sys) ll st ->
    Serializable sys step ll.

