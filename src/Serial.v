Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.

Section PerSystem.
  Variable sys: System.
  Variable step: Step TState TLabel.

  Definition History := list TLabel.

  Inductive HistoryOf: History -> Prop :=
  | Hist: forall ll st,
      steps step sys (getStateInit sys) ll st ->
      HistoryOf ll.

  (* Note that due to the definition of [TMsg], it is guaranteed that
   * an [Atomic] history is about a single transaction.
   * [TMsg] contains [tmsg_tid], and [In hdl mouts] in [AtomicCons]
   * ensures that the history is for a single transaction.
   *)
  Inductive Atomic: IdxT -> TMsg -> History -> list TMsg -> Prop :=
  | AtomicBase:
      forall hdl tid,
        tmsg_tid hdl = Some tid ->
        Atomic tid hdl nil (hdl :: nil)
  | AtomicCons:
      forall tid min hst mouts,
        Atomic tid min hst mouts ->
        forall hdl houts,
          In hdl mouts ->
          Atomic tid min (IlblOuts (Some hdl) houts :: hst)
                 (List.remove tmsg_dec hdl mouts ++ houts).

  Definition Transactional (hst: History) :=
    exists tid min mouts,
      isExternal sys (mid_from (msg_id (tmsg_msg min))) = true /\
      Atomic tid min hst mouts.

  Inductive Sequential: History -> Prop :=
  | SeqNil: Sequential nil
  | SeqIn:
      forall hst,
        Sequential hst ->
        forall msg tin,
          tin = IlblIn (toTMsgU msg) ->
          Sequential (tin :: hst)
  | SeqSeq:
      forall hst,
        Sequential hst ->
        forall trs,
          Transactional trs ->
          Sequential (trs ++ hst).

End PerSystem.

Definition Equivalent {LabelT} `{HasLabel LabelT} (ll1 ll2: list LabelT) :=
  behaviorOf ll1 = behaviorOf ll2.
Infix "≡" := Equivalent (at level 30).

Definition Serializable {StateT} `{HasInit StateT}
           (sys: System) (step: Step StateT TLabel) (ll: History) :=
  exists sll sst,
    (* 1) legal *) steps step sys (getStateInit sys) sll sst /\
    (* 2) sequential *) Sequential sys sll /\
    (* 3) equivalent *) ll ≡ sll.

(* A system is serializable when all possible behaviors are [Serializable]. *)
Definition SerializableSys {StateT} `{HasInit StateT}
           (sys: System) (step: Step StateT TLabel) :=
  forall ll st,
    steps step sys (getStateInit sys) ll st ->
    Serializable sys step ll.

