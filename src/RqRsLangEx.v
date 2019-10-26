Require Import Common Omega List ListSupport HVector FMap.
Require Import Syntax Topology Semantics SemFacts StepM Invariant Serial.

Require Export RqRsTopo RqRsFacts.
Require Export RqRsInvMsg RqRsInvLock RqRsInvSep RqRsInvAtomic.
Require Export RqRsMsgPredEx RqRsUtil.

Set Implicit Arguments.

Open Scope list.
Open Scope hvec.
Open Scope fmap.

Definition AtomicMsgOutsInv `{OStateIfc} (mp: MsgOutPred)
           (eouts: list (Id Msg)) (nst: MState): Prop :=
  Forall (fun eout => mp eout nst.(bst_oss) nst.(bst_orqs) nst.(bst_msgs)) eouts.

Definition AtomicInv `{OStateIfc} (mp: MsgOutPred):
  list (Id Msg) (* inits *) ->
  MState (* starting state *) ->
  MHistory (* atomic history *) ->
  list (Id Msg) (* eouts *) ->
  MState (* ending state *) -> Prop :=
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

