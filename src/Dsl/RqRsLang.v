Require Import Common Lia List ListSupport HVector FMap.
Require Import Syntax Topology Semantics SemFacts StepM Invariant Serial.

Require Export RqRsTopo RqRsFacts.
Require Export RqRsInvMsg RqRsInvLock RqRsInvSep RqRsInvAtomic.
Require Export RqRsMsgPred RqRsUtil.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Definition AtomicMsgOutsInv `{DecValue} `{OStateIfc} (mp: MsgOutPred)
           (eouts: list (Id Msg)) (nst: State): Prop :=
  Forall (fun eout => mp eout nst.(st_oss) nst.(st_orqs) nst.(st_msgs)) eouts.

Definition AtomicInv `{DecValue} `{OStateIfc} (mp: MsgOutPred):
  list (Id Msg) (* inits *) ->
  State (* starting state *) ->
  History (* atomic history *) ->
  list (Id Msg) (* eouts *) ->
  State (* ending state *) -> Prop :=
  fun inits st1 hst eouts st2 =>
    AtomicMsgOutsInv mp eouts st2.

Ltac disc_AtomicInv :=
  repeat
    match goal with
    | [H: AtomicInv _ _ _ _ _ _ |- _] => red in H; dest
    end.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

