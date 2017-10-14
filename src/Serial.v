Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics.

Section PerSystem.
  Variable sys: System.
  Variable step: Step TState TLabel.

  Definition History := list TLabel.

  Inductive HistoryOf: History -> Prop :=
  | Hist: forall ll st,
      steps step sys (getStateInit sys) ll st ->
      HistoryOf ll.

  Inductive Atomic: TMsg -> History -> list TMsg -> Prop :=
  | AtomicBase:
      forall min hlbl,
        iLblHdl hlbl = Some min ->
        Atomic min (hlbl :: nil) (iLblOuts hlbl)
  | AtomicCons:
      forall min hst mouts,
        Atomic min hst mouts ->
        forall hdl houts,
          In hdl mouts ->
          Atomic min (IlblInt (Some hdl) houts :: hst)
                 (List.remove tmsg_dec hdl mouts ++ houts).

  Definition Transactional (hst: History) :=
    hst = nil \/
    (exists min mouts,
        isExternal sys (mid_from (msg_id (tmsg_msg min))) = true /\
        Atomic min hst mouts).

  Definition Sequential (hst: History) :=
    exists (trs: list History),
      Forall Transactional trs /\ hst = concat trs.

End PerSystem.

Definition Equivalent {LabelT} `{HasLabel LabelT} (ll1 ll2: list LabelT) :=
  Permutation ll1 ll2 /\ behaviorOf ll1 = behaviorOf ll2.

Infix "≡" := Equivalent (at level 30).

Definition Serializable {StateT} `{HasInit StateT}
           (sys: System) (step: Step StateT TLabel) (ll: History) :=
  exists sll sst,
    (* 1) legal *) steps step sys (getStateInit sys) sll sst /\
    (* 2) sequential *) Sequential sys sll /\
    (* 3) equivalent *) ll ≡ sll.

(* A system is [Serial] when all possible behaviors are [Serializable]. *)
Definition Serial {StateT} `{HasInit StateT}
           (sys: System) (step: Step StateT TLabel) :=
  forall ll st,
    steps step sys (getStateInit sys) ll st ->
    Serializable sys step ll.

