Require Import Common Omega List ListSupport HVector FMap.
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
  Forall (fun eout => mp eout nst.(st_oss) nst.(st_orqs)) eouts.

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

Ltac atomic_cont_exfalso_bound msgOutPred :=
  exfalso;
  disc_rule_conds_ex;
  repeat 
    match goal with
    | [H1: AtomicMsgOutsInv _ ?eouts _, H2: In _ ?eouts |- _] =>
      red in H1; rewrite Forall_forall in H1;
      specialize (H1 _ H2); simpl in H1
    | [H: msgOutPred _ _ _ |- _] => red in H
    | [H1: caseDec _ ?sig _ _ |- _] =>
      match sig with
      | sigOf (?midx, ?msg) =>
        match goal with
        | [H2: msg_id ?msg = ?mid, H3: msg_type ?msg = ?mty |- _] =>
          progress replace sig with (midx, (mty, mid)) in H1
            by (unfold sigOf; simpl; rewrite H2, H3; reflexivity);
          simpl in H1
        end
      end
    end;
  assumption.

Ltac disc_msg_preds_with Hl Hin :=
  match type of Hl with
  | AtomicMsgOutsInv _ ?eouts _ =>
    red in Hl; rewrite Forall_forall in Hl;
    specialize (Hl _ Hin); simpl in Hl;
    red in Hl; disc_sig_caseDec
  end.

Ltac disc_msg_preds Hin :=
  match goal with
  | [H: AtomicMsgOutsInv _ _ _ |- _] =>
    let Hl := fresh "H" in
    pose proof H as Hl;
    disc_msg_preds_with Hl Hin
  end.

Close Scope list.
Close Scope hvec.
Close Scope fmap.

