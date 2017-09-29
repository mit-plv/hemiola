Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics.

Section PerSystem.
  Variable sys: System.
  Variable step: System -> State -> Label -> State -> Prop.

  Record HLabel :=
    { hlbl_hdl : Msg;
      hlbl_outs : list Msg
    }.

  Definition toHLabel (l: Label): option HLabel :=
    match l with
    | {| lbl_hdl := None |} => None
    | {| lbl_hdl := Some h; lbl_outs := outs |} =>
      Some {| hlbl_hdl := h; hlbl_outs := outs |}
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

  Definition AtomicTrs (hst: History) :=
    exists min mout,
      isTrsPair (msg_id min) (msg_id mout) = true /\
      Atomic min hst (mout :: nil).

  Definition IncompleteTrs (hst: History) :=
    exists min mouts,
      Forall (fun m => isInternal sys (msgTo (msg_id m)) = true) mouts /\
      Atomic min hst mouts.

  Definition Sequential (hst: History) :=
    exists (trs: list History),
      Forall (fun h => AtomicTrs h \/ IncompleteTrs h) trs /\
      hst = concat trs.

End PerSystem.

Definition insOf (obj: Object) (hst: History) :=
  filter (fun hl =>
            if obj_idx obj ==n msgFrom (msg_id (hlbl_hdl hl))
            then true else false) hst.

(* Two histories are equivalent if
 * 1) one history is a permutation of the other, and
 * 2) they have the same in-orders per an object.
 *)
Definition Equivalent (hst1 hst2: History) :=
  Permutation hst1 hst2 /\
  forall obj, insOf obj hst1 = insOf obj hst2.

Infix "≡" := Equivalent (at level 30).

Definition Serializable (sys: System) (hst shst: History) :=
  Sequential sys shst /\ Equivalent hst shst.

(* A system is [Serial] when all possible histories are [Serializable]. *)
Definition Serial (sys: System) (step: System -> State -> Label -> State -> Prop) :=
  forall hst,
    HistoryOf sys step hst ->
    exists shst, HistoryOf sys step shst /\
                 Serializable sys hst shst.

