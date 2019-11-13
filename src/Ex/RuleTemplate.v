Require Import List FMap Omega.
Require Import Common Topology Syntax IndexSupport.
Require Import RqRsLangEx. Import RqRsNotations.

Require Import Ex.TopoTemplate.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Record Miv :=
  { miv_id: IdxT;
    miv_value: Value }.
Notation "<| MID ; MV |>" := {| miv_id := MID; miv_value := MV |}.

Definition rqMsg (miv: Miv) :=
  {| msg_id := miv_id miv;
     msg_type := MRq;
     msg_value := miv_value miv |}.
Definition rsMsg (miv: Miv) :=
  {| msg_id := miv_id miv;
     msg_type := MRs;
     msg_value := miv_value miv |}.

Section Template.
  Variable (dtr: DTree).
  Context `{oifc: OStateIfc}.
  Variables (ridx msgId: IdxT).

  Definition immRule (prec: OPrec) (trs: OState -> OState): Rule :=
    rule[ridx]
    :requires (MsgsFrom nil /\ UpLockFree /\ DownLockFree /\ prec)
    :transition
       (do (st --> return {{ trs st.(ost), st.(orq), nil }})).

  (* Heads-up: [cidx] is not the index of itself, but of a child. *)
  Definition immDownRule (cidx: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg -> OState * Miv): Rule :=
    rule[ridx]
    :requires (MsgsFrom [rqUpFrom cidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ UpLockFree /\ DownLockFree /\ prec)
    :transition
       (do (st --> (msg <-- getFirstMsg st.(msgs);
                      nst ::= trs st.(ost) msg;
                    return {{ fst nst, st.(orq),
                              [(downTo cidx, rsMsg (snd nst))] }}))).
  
  Definition immUpRule (oidx: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg -> OState * Miv): Rule :=
    rule[ridx]
    :requires (MsgsFrom [downTo oidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ DownLockFree /\ prec)
    :transition
       (do (st --> (msg <-- getFirstMsg st.(msgs);
                      nst ::= trs st.(ost) msg;
                    return {{ fst nst, st.(orq),
                              [(rsUpFrom oidx, rsMsg (snd nst))] }}))).

  Definition rqUpUpRule (cidx oidx: IdxT)
             (prec: OState -> list (Id Msg) -> Prop)
             (trs: OState -> Msg -> Miv): Rule :=
    rule[ridx]
    :requires (MsgsFrom [rqUpFrom cidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ UpLockFree /\
               fun ost _ mins => prec ost mins)
    :transition
       (do (st --> (msg <-- getFirstMsg st.(msgs);
                      out ::= trs st.(ost) msg;
                    return {{ st.(ost),
                              addRq st.(orq) upRq msg [downTo oidx] (downTo cidx),
                              [(rqUpFrom oidx, rqMsg out)] }}))).

  Definition rqUpUpRuleS (oidx: IdxT)
             (prec: OState -> list (Id Msg) -> Prop)
             (trs: OState -> Miv): Rule :=
    rule[ridx]
    :requires (MsgsFrom nil /\ RqAccepting /\ UpLockFree /\
               fun ost _ mins => prec ost mins)
    :transition
       (do (st --> (out ::= trs st.(ost);
                    return {{ st.(ost),
                              addRqS st.(orq) upRq [downTo oidx],
                              [(rqUpFrom oidx, rqMsg out)] }}))).

  Definition RqUpDownSound (rcidx oidx: IdxT)
             (prec: OState -> list (Id Msg) -> Prop)
             (trs: OState -> Msg -> list IdxT * Miv): Prop :=
    forall ost min,
      prec ost [min] ->
      fst (trs ost (valOf min)) <> nil /\
      Forall (fun cidx => parentIdxOf dtr cidx = Some oidx) (fst (trs ost (valOf min))) /\
       ~ In rcidx (fst (trs ost (valOf min))).

  Definition rqUpDownRule (cidx oidx: IdxT)
             (prec: OState -> list (Id Msg) -> Prop)
             (trs: OState -> Msg -> list IdxT * Miv): Rule :=
    rule[ridx]
    :requires (MsgsFrom [rqUpFrom cidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ DownLockFree /\
               fun ost _ mins => prec ost mins)
    :transition
       (do (st -->
               (msg <-- getFirstMsg st.(msgs);
                  nst ::= trs st.(ost) msg;
                return {{ st.(ost),
                          addRq st.(orq) downRq msg
                                         (map rsUpFrom (fst nst)) (downTo cidx),
                          map (fun cidx => (downTo cidx, rqMsg (snd nst)))
                              (fst nst) }}))).

  Definition RqDownDownSound (oidx: IdxT)
             (prec: OState -> list (Id Msg) -> Prop)
             (trs: OState -> Msg -> list IdxT * Miv): Prop :=
    forall ost min,
      prec ost [min] ->
      fst (trs ost (valOf min)) <> nil /\
      Forall (fun cidx => parentIdxOf dtr cidx = Some oidx) (fst (trs ost (valOf min))).

  Definition rqDownDownRule (oidx: IdxT)
             (prec: OState -> list (Id Msg) -> Prop)
             (trs: OState -> Msg -> list IdxT * Miv): Rule :=
    rule[ridx]
    :requires (MsgsFrom [downTo oidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ DownLockFree /\
               fun ost _ mins => prec ost mins)
    :transition
       (do (st -->
               (msg <-- getFirstMsg st.(msgs);
                  nst ::= trs st.(ost) msg;
                return {{ st.(ost),
                          addRq st.(orq) downRq msg
                                         (map rsUpFrom (fst nst)) (rsUpFrom oidx),
                          map (fun cidx => (downTo cidx, rqMsg (snd nst)))
                              (fst nst) }}))).

  Definition rsDownDownRule (rqId: IdxT)
             (prec: OPrec)
             (trs: OState ->
                   Msg (* an incoming message *) ->
                   Msg (* the original request *) ->
                   IdxT (* response back to *) ->
                   OState * Miv) :=
    rule[ridx]
    :requires (MsgsFromORq upRq /\ MsgIdsFrom [msgId] /\
               UpLockMsgId MRq rqId /\ UpLockIdxBack /\
               RsAccepting /\ DownLockFree /\ prec)
    :transition
       (do (st --> (msg <-- getFirstMsg st.(msgs);
                      rq <-- getUpLockMsg st.(orq);
                      rsbTo <-- getUpLockIdxBack st.(orq);
                      nst ::= trs st.(ost) msg rq rsbTo;
                    return {{ fst nst,
                              removeRq st.(orq) upRq,
                              [(rsbTo, rsMsg (snd nst))] }}))).

  Definition rsDownDownRuleS (prec: OPrec)
             (trs: OState ->
                   Msg (* an incoming message *) ->
                   OState) :=
    rule[ridx]
    :requires (MsgsFromORq upRq /\ MsgIdsFrom [msgId] /\
               UpLockBackNone /\ RsAccepting /\ DownLockFree /\ prec)
    :transition
       (do (st --> (msg <-- getFirstMsg st.(msgs);
                      nst ::= trs st.(ost) msg;
                    return {{ nst, removeRq st.(orq) upRq, nil }}))).

  Definition rsUpDownRule (rqId: IdxT)
             (prec: OPrec)
             (trs: OState ->
                   list (Id Msg) (* incoming messages *) ->
                   Msg (* the original request *) ->
                   IdxT (* response back to *) ->
                   OState * Miv) :=
    rule[ridx]
    :requires (MsgsFromORq downRq /\ MsgIdFromEach msgId /\
               DownLockMsgId MRq rqId /\ DownLockIdxBack /\
               RsAccepting /\ prec)
    :transition
       (do (st --> (rq <-- getDownLockMsg st.(orq);
                      rsbTo <-- getDownLockIdxBack st.(orq);
                      nst ::= trs st.(ost) st.(msgs) rq rsbTo;
                    return {{ fst nst,
                              removeRq st.(orq) downRq,
                              [(rsbTo, rsMsg (snd nst))] }}))).

  Definition rsUpDownRuleOne (rqId: IdxT)
             (prec: OPrec)
             (trs: OState ->
                   Id Msg (* an incoming message *) ->
                   Msg (* the original request *) ->
                   IdxT (* response back to *) ->
                   OState * Miv) :=
    rule[ridx]
    :requires (MsgsFromORq downRq /\ MsgIdsFrom [msgId] /\
               DownLockMsgId MRq rqId /\ DownLockIdxBack /\
               RsAccepting /\ prec)
    :transition
       (do (st --> (idm <-- getFirstIdMsg st.(msgs);
                      rq <-- getDownLockMsg st.(orq);
                      rsbTo <-- getDownLockIdxBack st.(orq);
                      nst ::= trs st.(ost) idm rq rsbTo;
                    return {{ fst nst,
                              removeRq st.(orq) downRq,
                              [(rsbTo, rsMsg (snd nst))] }}))).
  
  Definition rsUpUpRule (rqId: IdxT)
             (prec: OPrec)
             (trs: OState ->
                   list (Id Msg) (* incoming messages *) ->
                   Msg (* the original request *) ->
                   IdxT (* response back to *) ->
                   OState * Miv) :=
    rule[ridx]
    :requires (MsgsFromORq downRq /\ MsgIdFromEach msgId /\
               DownLockMsgId MRq rqId /\ DownLockIdxBack /\
               RsAccepting /\ prec)
    :transition
       (do (st --> (rq <-- getDownLockMsg st.(orq);
                      rsbTo <-- getDownLockIdxBack st.(orq);
                      nst ::= trs st.(ost) st.(msgs) rq rsbTo;
                    return {{ fst nst,
                              removeRq st.(orq) downRq,
                              [(rsbTo, rsMsg (snd nst))] }}))).

  Definition rsUpUpRuleOne (rqId: IdxT)
             (prec: OPrec)
             (trs: OState ->
                   Id Msg (* an incoming message *) ->
                   Msg (* the original request *) ->
                   IdxT (* response back to *) ->
                   OState * Miv) :=
    rule[ridx]
    :requires (MsgsFromORq downRq /\ MsgIdsFrom [msgId] /\
               DownLockMsgId MRq rqId /\ DownLockIdxBack /\
               RsAccepting /\ prec)
    :transition
       (do (st --> (idm <-- getFirstIdMsg st.(msgs);
                      rq <-- getDownLockMsg st.(orq);
                      rsbTo <-- getDownLockIdxBack st.(orq);
                      nst ::= trs st.(ost) idm rq rsbTo;
                    return {{ fst nst,
                              removeRq st.(orq) downRq,
                              [(rsbTo, rsMsg (snd nst))] }}))).

  Definition RsDownRqDownSoundPrec (oidx: IdxT) (orq: ORq Msg)
             (outInds: list IdxT): Prop :=
    orq@[upRq] >>=[True]
       (fun rqiu =>
          exists rcidx rqUp,
            parentIdxOf dtr rcidx = Some oidx /\
            rqEdgeUpFrom dtr rcidx = Some rqUp /\
            (orq@[upRq] >>=[True] (fun rqiu => edgeDownTo dtr rcidx = rqiu.(rqi_midx_rsb))) /\
            ~ In rcidx outInds).
  
  Definition RsDownRqDownSound (sys: System) (oidx: IdxT)
             (prec: OPrec) (trs: OState -> Msg -> OState * (list IdxT * Miv)): Prop :=
    forall ost orq rsin,
      prec ost orq [rsin] ->
      orq@[upRq] >>=[True]
         (fun rqiu =>
            forall rq,
              rqiu.(rqi_msg) = Some rq ->
              fst (snd (trs ost rq)) <> nil /\
              Forall (fun cidx => parentIdxOf dtr cidx = Some oidx) (fst (snd (trs ost rq))) /\
              exists rcidx rqUp,
                parentIdxOf dtr rcidx = Some oidx /\
                rqEdgeUpFrom dtr rcidx = Some rqUp /\
                edgeDownTo dtr rcidx = rqiu.(rqi_midx_rsb) /\
                In rcidx (map (@obj_idx _) (sys_objs sys)) /\
                ~ In rcidx (fst (snd (trs ost rq)))).

  Definition rsDownRqDownRule (oidx: IdxT) (rqId: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg -> OState * (list IdxT * Miv)) :=
    rule[ridx]
    :requires (MsgsFromORq upRq /\ MsgIdsFrom [msgId] /\
               UpLockMsgId MRq rqId /\ UpLockIdxBack /\
               RsAccepting /\ DownLockFree /\ prec)
    :transition
       (do (st --> (rq <-- getUpLockMsg st.(orq);
                      rsbTo <-- getUpLockIdxBack st.(orq);
                      nst ::= trs st.(ost) rq;
                    return {{ fst nst,
                              addRq (removeRq st.(orq) upRq)
                                    downRq rq (map rsUpFrom (fst (snd nst))) rsbTo,
                              map (fun cidx => (downTo cidx, rqMsg (snd (snd nst))))
                                  (fst (snd nst)) }}))).
  
End Template.

Notation "'rule.imm' '[' RIDX ']' ':requires' PREC ':transition' TRS" :=
  (immRule RIDX PREC TRS%trs) (at level 5, only parsing).
Notation "'rule.immd' '[' RIDX ']' ':accepts' MSGID ':from' FROM ':requires' PREC ':transition' TRS" :=
  (immDownRule RIDX MSGID FROM PREC TRS%trs) (at level 5, only parsing).
Notation "'rule.immu' '[' RIDX ']' ':accepts' MSGID ':me' ME ':requires' PREC ':transition' TRS" :=
  (immUpRule RIDX MSGID ME PREC TRS%trs) (at level 5).

Notation "'rule.rquu' '[' RIDX ']' ':accepts' MSGID ':from' FROM ':me' ME ':requires' PREC ':transition' TRS" :=
  (rqUpUpRule RIDX MSGID FROM ME PREC TRS%trs) (at level 5).
Notation "'rule.rqu' '[' RIDX ']' ':me' ME ':requires' PREC ':transition' TRS" :=
  (rqUpUpRuleS RIDX ME PREC TRS%trs) (at level 5).
Notation "'rule.rqud' '[' RIDX ']' ':accepts' MSGID ':from' FROM ':me' ME ':requires' PREC ':transition' TRS" :=
  (rqUpDownRule RIDX MSGID FROM ME PREC TRS%trs) (at level 5).
Notation "'rule.rqdd' '[' RIDX ']' ':accepts' MSGID ':me' ME ':requires' PREC ':transition' TRS" :=
  (rqDownDownRule RIDX MSGID ME PREC TRS%trs) (at level 5).

Notation "'rule.rsdd' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsDownDownRule RIDX MSGID RQID PREC TRS%trs) (at level 5).
Notation "'rule.rsd' '[' RIDX ']' ':accepts' MSGID ':requires' PREC ':transition' TRS" :=
  (rsDownDownRuleS RIDX MSGID PREC TRS%trs) (at level 5).
Notation "'rule.rsud' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsUpDownRule RIDX MSGID RQID PREC TRS%trs) (at level 5).
Notation "'rule.rsudo' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsUpDownRuleOne RIDX MSGID RQID PREC TRS%trs) (at level 5).
Notation "'rule.rsuu' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsUpUpRule RIDX MSGID RQID PREC TRS%trs) (at level 5).
Notation "'rule.rsuuo' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsUpUpRuleOne RIDX MSGID RQID PREC TRS%trs) (at level 5).

Notation "'rule.rsrq' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':me' ME ':requires' PREC ':transition' TRS" :=
  (rsDownRqDownRule RIDX MSGID ME RQID PREC TRS%trs) (at level 5).

Hint Unfold rqMsg rsMsg: RuleConds.

Section Facts.
  Variable (dtr: DTree).
  Hypothesis (Hdtr: TreeTopo dtr).
  Context `{oifc: OStateIfc}.

  Lemma immRule_ImmDownRule:
    forall oidx ridx prec trs,
      ImmDownRule dtr oidx (immRule ridx prec trs).
  Proof.
    unfold immRule; intros; repeat split; solve_rule_conds_ex.
    - destruct ins; [constructor|discriminate].
    - left; repeat split.
      destruct rins; [reflexivity|discriminate].
  Qed.

  Lemma immDownRule_ImmDownRule:
    forall oidx ridx msgId cidx prec trs,
      parentIdxOf dtr cidx = Some oidx ->
      ImmDownRule dtr oidx (immDownRule ridx msgId cidx prec trs).
  Proof.
    unfold immDownRule; intros; repeat split; solve_rule_conds_ex.
    right; solve_rule_conds_ex.
    - apply Hdtr in H; dest; assumption.
    - apply Hdtr in H; dest; assumption.
  Qed.

  Lemma immUpRule_ImmUpRule:
    forall oidx ridx msgId cidx prec trs,
      parentIdxOf dtr cidx = Some oidx ->
      ImmUpRule dtr cidx (immUpRule ridx msgId cidx prec trs).
  Proof.
    unfold immUpRule; intros; repeat split; solve_rule_conds_ex.
    - apply Hdtr in H; dest; assumption.
    - apply Hdtr in H; dest; assumption.
  Qed.

  Lemma rqUpUpRule_RqFwdRule:
    forall sys oidx pidx ridx msgId cidx prec trs,
      parentIdxOf dtr cidx = Some oidx ->
      parentIdxOf dtr oidx = Some pidx ->
      RqFwdRule dtr sys oidx (rqUpUpRule ridx msgId cidx oidx prec trs).
  Proof.
    unfold rqUpUpRule; intros; split.
    - repeat split; solve_rule_conds_ex.
      destruct (idm <-- hd_error mins; Some (valOf idm))%trs;
        reflexivity.
    - left; repeat split; solve_rule_conds_ex.
      right; solve_rule_conds_ex.
      + apply Hdtr in H; dest; assumption.
      + apply Hdtr in H; dest; assumption.
      + apply Hdtr in H0; dest; assumption.
      + apply Hdtr in H0; dest; assumption.
  Qed.

  Lemma rqUpUpRuleS_RqFwdRule:
    forall sys oidx pidx ridx prec trs,
      parentIdxOf dtr oidx = Some pidx ->
      RqFwdRule dtr sys oidx (rqUpUpRuleS ridx oidx prec trs).
  Proof.
    unfold rqUpUpRuleS; intros; split.
    - repeat split; solve_rule_conds_ex.
    - left; repeat split; solve_rule_conds_ex.
      + unfold addRqS; mred.
      + left; solve_rule_conds_ex.
        * destruct rins; [reflexivity|discriminate].
        * apply Hdtr in H; dest; assumption.
        * apply Hdtr in H; dest; assumption.
  Qed.

  Lemma rqUpDownRule_RqFwdRule:
    forall sys oidx ridx msgId cidx
           (prec: OState -> list (Id Msg) -> Prop)
           (trs: OState -> Msg -> list IdxT * Miv),
      In cidx (map (@obj_idx _) (sys_objs sys)) ->
      parentIdxOf dtr cidx = Some oidx ->
      RqUpDownSound dtr cidx oidx prec trs ->
      RqFwdRule dtr sys oidx (rqUpDownRule ridx msgId cidx oidx prec trs).
  Proof.
    unfold rqUpDownRule; intros; split.
    - repeat split; solve_rule_conds_ex.
      + apply Forall_forall; intros msg ?.
        apply in_map_iff in H2.
        destruct H2 as [midx ?]; dest; subst; reflexivity.
      + destruct (idm <-- hd_error mins; Some (valOf idm))%trs;
          reflexivity.
    - apply in_map_iff in H.
      destruct H as [upCObj [? ?]]; dest; subst.
      right; left; repeat red; repeat ssplit.
      + solve_rule_conds_ex.
      + solve_rule_conds_ex.
      + solve_rule_conds_ex.
      + solve_rule_conds_ex.
        * apply Hdtr in H0; dest; assumption.
        * apply Hdtr in H0; dest; assumption.
        * specialize (H1 _ _ H4); dest.
          eapply H1; eauto.
          simpl; destruct (fst (trs nost rmsg)); [auto|discriminate].
        * unfold idsOf; repeat rewrite map_length; reflexivity.
        * specialize (H1 _ _ H4); dest; simpl in *.
          apply Forall_forall; intros [rqTo rsFrom] ?; simpl.
          clear -Hdtr H1 H5 H6.
          induction (fst (trs nost rmsg)) as [|cidx cinds]; [exfalso; auto|].
          inv H1; simpl in *.
          destruct H6; dest.
          { inv H; destruct Hdtr as [[? ?] ?].
            specialize (H _ _ H2); dest.
            exists cidx; repeat split; try assumption.
            intro Hx; subst; auto.
          }
          { eapply IHcinds; eauto. }
  Qed.

  Lemma rqDownDownRule_RqFwdRule:
    forall sys oidx pidx ridx msgId prec trs,
      parentIdxOf dtr oidx = Some pidx ->
      RqDownDownSound dtr oidx prec trs ->
      RqFwdRule dtr sys oidx (rqDownDownRule ridx msgId oidx prec trs).
  Proof.
    unfold rqDownDownRule; intros; split.
    - repeat split; solve_rule_conds_ex.
      + apply Forall_forall; intros msg ?.
        apply in_map_iff in H1.
        destruct H1 as [midx ?]; dest; subst; reflexivity.
      + destruct (idm <-- hd_error mins; Some (valOf idm))%trs;
          reflexivity.
    - right; right; repeat red; repeat ssplit.
      + solve_rule_conds_ex.
      + solve_rule_conds_ex.
      + solve_rule_conds_ex.
      + solve_rule_conds_ex.
        * apply Hdtr in H; dest; assumption.
        * apply Hdtr in H; dest; assumption.
        * specialize (H0 _ _ H3); dest; simpl in *.
          destruct (fst (trs nost rmsg)); [auto|discriminate].
        * unfold idsOf; repeat rewrite map_length; reflexivity.
        * specialize (H0 _ _ H3); dest; simpl in *.
          apply Forall_forall; intros [rqTo rsFrom] ?; simpl.
          clear -Hdtr H1 H4.
          induction (fst (trs nost rmsg)) as [|cidx cinds]; [dest_in|].
          inv H1; simpl in H4; destruct H4; dest.
          { inv H; destruct Hdtr as [[? ?] ?].
            specialize (H _ _ H2); dest.
            exists cidx; repeat split; assumption.
          }
          { eapply IHcinds; eauto. }
  Qed.

  Lemma rsDownDownRule_RsBackRule:
    forall ridx msgId rqId prec trs,
      RsBackRule (rsDownDownRule ridx msgId rqId prec trs).
  Proof.
    unfold rsDownDownRule; intros; split.
    - left; repeat red; repeat ssplit; solve_rule_conds_ex.
    - repeat red; repeat ssplit; solve_rule_conds_ex.
  Qed.

  Lemma rsDownDownRuleS_RsBackRule:
    forall ridx msgId prec trs,
      RsBackRule (rsDownDownRuleS ridx msgId prec trs).
  Proof.
    unfold rsDownDownRuleS; intros; split.
    - left; repeat red; repeat ssplit; solve_rule_conds_ex.
    - repeat red; repeat ssplit; solve_rule_conds_ex.
  Qed.

  Lemma rsUpDownRule_RsBackRule:
    forall ridx msgId rqId prec trs,
      RsBackRule (rsUpDownRule ridx msgId rqId prec trs).
  Proof.
    unfold rsUpDownRule; intros; split.
    - right; repeat red; repeat ssplit; solve_rule_conds_ex.
    - repeat red; repeat ssplit; solve_rule_conds_ex.
  Qed.

  Lemma rsUpDownRuleOne_RsBackRule:
    forall ridx msgId rqId prec trs,
      RsBackRule (rsUpDownRuleOne ridx msgId rqId prec trs).
  Proof.
    unfold rsUpDownRule; intros; split.
    - right; repeat red; repeat ssplit; solve_rule_conds_ex.
    - repeat red; repeat ssplit; solve_rule_conds_ex.
  Qed.

  Lemma rsUpUpRule_RsBackRule:
    forall ridx msgId rqId prec trs,
      RsBackRule (rsUpUpRule ridx msgId rqId prec trs).
  Proof.
    unfold rsUpUpRule; intros; split.
    - right; repeat red; repeat ssplit; solve_rule_conds_ex.
    - repeat red; repeat ssplit; solve_rule_conds_ex.
  Qed.

  Lemma rsUpUpRuleOne_RsBackRule:
    forall ridx msgId rqId prec trs,
      RsBackRule (rsUpUpRuleOne ridx msgId rqId prec trs).
  Proof.
    unfold rsUpUpRule; intros; split.
    - right; repeat red; repeat ssplit; solve_rule_conds_ex.
    - repeat red; repeat ssplit; solve_rule_conds_ex.
  Qed.

  Lemma rsDownRqDownRule_RsDownRqDownRule:
    forall sys oidx ridx msgId rqId prec trs,
      RsDownRqDownSound dtr sys oidx prec trs ->
      RsDownRqDownRule dtr sys oidx (rsDownRqDownRule ridx msgId oidx rqId prec trs).
  Proof.
    unfold rsDownRqDownRule; intros; red; repeat ssplit.
    - solve_rule_conds_ex.
    - solve_rule_conds_ex.
    - solve_rule_conds_ex.
      apply Forall_forall; intros rq ?.
      apply in_map_iff in H2.
      destruct H2 as [midx ?]; dest; subst; reflexivity.
    - red; intros; simpl in *.
      disc_rule_conds_ex.
      specialize (H _ _ _ H7).
      rewrite Hrqi in H; simpl in H.
      specialize (H _ Hmsg).
      destruct H as [? [? [rcidx [rqUp ?]]]]; dest.
      disc_rule_conds_ex.
      apply in_map_iff in H10; destruct H10 as [upCObj [? ?]]; subst.

      (* NOTE: [eexists] in [solve_rule_conds_ex] does not work here,
       * so we provide the existence manually. *)
      do 5 eexists; repeat ssplit.
      4, 5: reflexivity.
      3: solve_rule_conds_ex.
      2: {
        exists rqi.
        exists {| rqi_msg := Some msg;
                  rqi_minds_rss := map rsUpFrom (fst (snd (trs post msg)));
                  rqi_midx_rsb := Some idx |}.
        solve_rule_conds_ex.
      }
      1: {
        solve_rule_conds_ex.
        { destruct (fst (snd (trs post msg))); [auto|discriminate]. }
        { unfold idsOf; repeat rewrite map_length; reflexivity. }
        { apply Forall_forall; intros [rqTo rsFrom] ?; simpl.
          clear -Hdtr H2 H10 H11.
          induction (fst (snd (trs post msg))) as [|cidx cinds]; [dest_in|].
          inv H2; simpl in H10; destruct H10; dest.
          { inv H; destruct Hdtr as [[? ?] ?].
            specialize (H _ _ H1); dest.
            exists cidx; repeat split; try assumption.
            intro Hx; subst; elim H11; left; reflexivity.
          }
          { eapply IHcinds; eauto.
            intro Hx; elim H11; right; assumption.
          } 
        }
      }
  Qed.

End Facts.

