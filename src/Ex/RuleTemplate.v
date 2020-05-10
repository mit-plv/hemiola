Require Import List FMap Omega.
Require Import Common Topology Syntax IndexSupport.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.TopoTemplate.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Record Miv `{DecValue} :=
  { miv_id: IdxT;
    miv_value: t_type }.
Notation "<| MID ; MV |>" := {| miv_id := MID; miv_value := MV |}.

Definition rqMsg `{DecValue} (addr: AddrT) (miv: Miv) :=
  {| msg_id := miv_id miv;
     msg_type := MRq;
     msg_addr := addr;
     msg_value := miv_value miv |}.
Definition rsMsg `{DecValue} (addr: AddrT) (miv: Miv) :=
  {| msg_id := miv_id miv;
     msg_type := MRs;
     msg_addr := addr;
     msg_value := miv_value miv |}.

Section Template.
  Variable (dtr: DTree).
  Context `{dv:DecValue} `{oifc: OStateIfc}.
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
                              [(downTo cidx, rsMsg msg.(msg_addr) (snd nst))] }}))).

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
                              [(rsUpFrom oidx, rsMsg msg.(msg_addr) (snd nst))] }}))).

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
                              [(rqUpFrom oidx, rqMsg msg.(msg_addr) out)] }}))).

  Definition rqUpUpRuleS (oidx: IdxT)
             (prec: OState -> Prop)
             (trs: OState -> Miv): Rule :=
    rule[ridx]
    :requires (MsgsFrom nil /\ RqAccepting /\ UpLockFree /\
               fun ost _ _ => prec ost)
    :transition
       (do (st --> (out ::= trs st.(ost);
                    return {{ st.(ost),
                              addRqS st.(orq) upRq [downTo oidx],
                              [(rqUpFrom oidx, rqMsg tt out)] }}))).

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
                          map (fun cidx => (downTo cidx, rqMsg msg.(msg_addr) (snd nst)))
                              (fst nst) }}))).

  Definition RqUpDownSoundS (oidx: IdxT)
             (prec: OState -> Prop)
             (trs: OState -> list IdxT * Miv): Prop :=
    forall ost,
      prec ost ->
      fst (trs ost) <> nil /\
      Forall (fun cidx => parentIdxOf dtr cidx = Some oidx) (fst (trs ost)).

  Definition rqUpDownRuleS (oidx: IdxT) (prec: OState -> Prop)
             (trs: OState -> list IdxT * Miv): Rule :=
    rule[ridx]
    :requires (MsgsFrom nil /\ RqAccepting /\ DownLockFree /\
               fun ost _ _ => prec ost)
    :transition
       (do (st -->
               (nst ::= trs st.(ost);
                return {{ st.(ost),
                          addRqS st.(orq) downRq (map rsUpFrom (fst nst)),
                          map (fun cidx => (downTo cidx, rqMsg tt (snd nst)))
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
                          map (fun cidx => (downTo cidx, rqMsg msg.(msg_addr) (snd nst)))
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
                              [(rsbTo, rsMsg msg.(msg_addr) (snd nst))] }}))).

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
                              [(rsbTo, rsMsg rq.(msg_addr) (snd nst))] }}))).

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
                              [(rsbTo, rsMsg rq.(msg_addr) (snd nst))] }}))).

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
                              [(rsbTo, rsMsg rq.(msg_addr) (snd nst))] }}))).

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
                              [(rsbTo, rsMsg rq.(msg_addr) (snd nst))] }}))).

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
             (prec: OPrec) (trs: OState -> Msg -> IdxT -> OState * (list IdxT * Miv)): Prop :=
    forall ost orq rsin,
      prec ost orq [rsin] ->
      orq@[upRq] >>=[True]
         (fun rqiu =>
            forall rq rsbTo,
              rqiu.(rqi_msg) = Some rq ->
              rqiu.(rqi_midx_rsb) = Some rsbTo ->
              fst (snd (trs ost rq rsbTo)) <> nil /\
              Forall (fun cidx => parentIdxOf dtr cidx = Some oidx)
                     (fst (snd (trs ost rq rsbTo))) /\
              exists rcidx rqUp,
                parentIdxOf dtr rcidx = Some oidx /\
                rqEdgeUpFrom dtr rcidx = Some rqUp /\
                edgeDownTo dtr rcidx = rqiu.(rqi_midx_rsb) /\
                In rcidx (map obj_idx (sys_objs sys)) /\
                ~ In rcidx (fst (snd (trs ost rq rsbTo)))).

  Definition rsDownRqDownRule (oidx: IdxT) (rqId: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg (* rq *) -> IdxT (* rsbTo *) ->
                   OState * (list IdxT * Miv)) :=
    rule[ridx]
    :requires (MsgsFromORq upRq /\ MsgIdsFrom [msgId] /\
               UpLockMsgId MRq rqId /\ UpLockIdxBack /\
               RsAccepting /\ DownLockFree /\ prec)
    :transition
       (do (st --> (rq <-- getUpLockMsg st.(orq);
                   rsbTo <-- getUpLockIdxBack st.(orq);
                   nst ::= trs st.(ost) rq rsbTo;
                    return {{ fst nst,
                              addRq (removeRq st.(orq) upRq)
                                    downRq rq (map rsUpFrom (fst (snd nst))) rsbTo,
                              map (fun cidx => (downTo cidx,
                                                rqMsg rq.(msg_addr) (snd (snd nst))))
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
Notation "'rule.rqsu' '[' RIDX ']' ':me' ME ':requires' PREC ':transition' TRS" :=
  (rqUpUpRuleS RIDX ME PREC TRS%trs) (at level 5).
Notation "'rule.rqud' '[' RIDX ']' ':accepts' MSGID ':from' FROM ':me' ME ':requires' PREC ':transition' TRS" :=
  (rqUpDownRule RIDX MSGID FROM ME PREC TRS%trs) (at level 5).
Notation "'rule.rqsd' '[' RIDX ']' ':me' ME ':requires' PREC ':transition' TRS" :=
  (rqUpDownRuleS RIDX ME PREC TRS%trs) (at level 5).
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
  Context `{dv: DecValue} `{oifc: OStateIfc}.

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
      left; solve_rule_conds_ex.
      + destruct rins; [reflexivity|discriminate].
      + apply Hdtr in H; dest; assumption.
      + apply Hdtr in H; dest; assumption.
  Qed.

  Lemma rqUpDownRule_RqFwdRule:
    forall sys oidx ridx msgId cidx
           (prec: OState -> list (Id Msg) -> Prop)
           (trs: OState -> Msg -> list IdxT * Miv),
      In cidx (map obj_idx (sys_objs sys)) ->
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
        right; solve_rule_conds_ex.
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

  Lemma rqUpDownRuleS_RqFwdRule:
    forall sys oidx ridx (prec: OState -> Prop)
           (trs: OState -> list IdxT * Miv),
      RqUpDownSoundS dtr oidx prec trs ->
      RqFwdRule dtr sys oidx (rqUpDownRuleS ridx oidx prec trs).
  Proof.
    unfold rqUpDownRuleS; intros; split.
    - repeat split; solve_rule_conds_ex.
      apply Forall_forall; intros msg ?.
      apply in_map_iff in H4.
      destruct H4 as [midx ?]; dest; subst; reflexivity.
    - right; left; repeat red; repeat ssplit.
      + solve_rule_conds_ex.
      + solve_rule_conds_ex.
      + solve_rule_conds_ex.
      + solve_rule_conds_ex.
        left; solve_rule_conds_ex.
        * destruct rins; [reflexivity|discriminate].
        * specialize (H _ H3); dest.
          eapply H.
          destruct (fst (trs nost)); [auto|discriminate].
        * unfold idsOf; repeat rewrite map_length; reflexivity.
        * specialize (H _ H3); dest; simpl in *.
          apply Forall_forall; intros [rqTo rsFrom] ?; simpl.
          clear -Hdtr H4 H5.
          induction (fst (trs nost)) as [|cidx cinds]; [exfalso; auto|].
          inv H4; inv H5; simpl in *; dest.
          { inv H; destruct Hdtr as [[? ?] ?].
            specialize (H _ _ H1); dest.
            exists cidx; repeat split; try assumption.
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
      specialize (H _ _ Hmsg Hidx).
      destruct H as [? [? [rcidx [rqUp ?]]]]; dest.
      disc_rule_conds_ex.
      apply in_map_iff in H10; destruct H10 as [upCObj [? ?]]; subst.
      destruct (rqi_rss rqi) as [|[rsF rsV] rss] eqn:Hrss; [discriminate|].
      destruct rss; [|discriminate].
      simpl in *; inv H0.

      (* NOTE: [eexists] in [solve_rule_conds_ex] does not work here,
       * so we provide the existence manually. *)
      exists (rsF, rsV); do 4 eexists; repeat ssplit.
      4, 5: reflexivity.
      3: solve_rule_conds_ex.
      2: {
        exists rqi.
        exists {| rqi_msg := Some msg;
                  rqi_rss := map (fun rs => (rs, None))
                                 (map rsUpFrom (fst (snd (trs post msg idx))));
                  rqi_midx_rsb := Some idx |}.
        solve_rule_conds_ex.
      }
      1: {
        solve_rule_conds_ex.
        { destruct (fst (snd (trs post msg idx))); [auto|discriminate]. }
        { unfold idsOf; repeat rewrite map_length; reflexivity. }
        { apply Forall_forall; intros [rqTo rsFrom] ?; simpl.
          clear -Hdtr H0 H2 H11.
          induction (fst (snd (trs post msg idx))) as [|cidx cinds]; [dest_in|].
          inv H2; simpl in H0; destruct H0; dest.
          { inv H; destruct Hdtr as [[? ?] ?].
            specialize (H _ _ H3); dest.
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

Section DecValue.
  Context `{dv: DecValue} `{OStateIfc}.

  Lemma tree2Topo_immRule_not_RqToUpRule:
    forall tr bidx oidx ridx prec trs ost orq ins,
      rule_precond (immRule ridx prec trs) ost orq ins ->
      ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (immRule ridx prec trs).
  Proof.
    intros; intro.
    destruct H1.
    red in H2; dest.
    clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
    specialize (H5 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H5 _ _ _ eq_refl); dest; discriminate.
  Qed.

  Lemma tree2Topo_immDownRule_not_RqToUpRule:
    forall tr bidx oidx ridx msgId cidx prec trs ost orq ins,
      rule_precond (immDownRule ridx msgId cidx prec trs) ost orq ins ->
      ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (immDownRule ridx msgId cidx prec trs).
  Proof.
    intros; intro.
    destruct H1.
    red in H2; dest.
    clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
    specialize (H5 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H5 _ _ _ eq_refl); dest.
    destruct H0.
    - dest; discriminate.
    - dest; disc_rule_conds_ex.
      apply rqEdgeUpFrom_rqUpFrom in H7; discriminate.
  Qed.

  Lemma tree2Topo_immUpRule_not_RqToUpRule:
    forall tr bidx oidx ridx msgId prec trs ost orq ins,
      rule_precond (immUpRule ridx msgId oidx prec trs) ost orq ins ->
      ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (immUpRule ridx msgId oidx prec trs).
  Proof.
    intros; intro.
    destruct H1.
    red in H2; dest.
    clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
    specialize (H5 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H5 _ _ _ eq_refl); dest.
    destruct H0.
    - dest; discriminate.
    - dest; disc_rule_conds_ex.
      apply rqEdgeUpFrom_rqUpFrom in H6; discriminate.
  Qed.

  Lemma tree2Topo_rqUpDownRule_not_RqToUpRule:
    forall tr bidx cidx oidx ridx msgId prec trs ost orq ins,
      rule_precond (rqUpDownRule ridx msgId cidx oidx prec trs) ost orq ins ->
      ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rqUpDownRule ridx msgId cidx oidx prec trs).
  Proof.
    intros; intro.
    destruct H1.
    red in H2; dest.
    clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
    specialize (H5 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H5 _ _ _ eq_refl); dest.
    destruct H0.
    - dest; discriminate.
    - dest; disc_rule_conds_ex.
      destruct (fst (trs ost x4)); [discriminate|].
      inv H1; apply rqEdgeUpFrom_rqUpFrom in H6; discriminate.
  Qed.

  Lemma tree2Topo_rqDownDownRule_not_RqToUpRule:
    forall tr bidx oidx ridx msgId prec trs ost orq ins,
      rule_precond (rqDownDownRule ridx msgId oidx prec trs) ost orq ins ->
      ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rqDownDownRule ridx msgId oidx prec trs).
  Proof.
    intros; intro.
    destruct H1.
    red in H2; dest.
    clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
    specialize (H5 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H5 _ _ _ eq_refl); dest.
    destruct H0.
    - dest; discriminate.
    - dest; disc_rule_conds_ex.
      destruct (fst (trs ost x4)); [discriminate|].
      inv H1; apply rqEdgeUpFrom_rqUpFrom in H6; discriminate.
  Qed.

  Lemma tree2Topo_rsDownDownRule_not_RqToUpRule:
    forall tr bidx oidx ridx msgId rqId prec trs ost orq ins,
      rule_precond (rsDownDownRule ridx msgId rqId prec trs) ost orq ins ->
      ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rsDownDownRule ridx msgId rqId prec trs).
  Proof.
    intros; intro.
    destruct H1.
    red in H2; dest.
    clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
    specialize (H5 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H5 _ _ _ eq_refl); dest.
    destruct H2.
    - dest; discriminate.
    - dest; disc_rule_conds_ex.
      clear -H5.
      apply f_equal with (f:= fun m => m@[upRq]) in H5; mred.
  Qed.

  Lemma tree2Topo_rsDownDownRuleS_not_RqToUpRule:
    forall tr bidx oidx ridx msgId prec trs ost orq ins,
      rule_precond (rsDownDownRuleS ridx msgId prec trs) ost orq ins ->
      ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rsDownDownRuleS ridx msgId prec trs).
  Proof.
    intros; intro.
    destruct H1.
    red in H2; dest.
    clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
    specialize (H5 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H5 _ _ _ eq_refl); dest.
    destruct H3.
    - dest; discriminate.
    - dest; disc_rule_conds_ex.
      clear -H7.
      apply f_equal with (f:= fun m => m@[upRq]) in H7; mred.
  Qed.

  Lemma tree2Topo_rsUpDownRule_not_RqToUpRule:
    forall tr bidx oidx ridx msgId rqId prec trs ost orq ins,
      rule_precond (rsUpDownRule ridx msgId rqId prec trs) ost orq ins ->
      ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rsUpDownRule ridx msgId rqId prec trs).
  Proof.
    intros; intro.
    destruct H1.
    red in H1; dest.
    clear -H0 H3. (* [rule_precond] and [RqReleasing] *)
    specialize (H3 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H3 _ _ _ eq_refl).
    inv H3; discriminate.
  Qed.

  Lemma tree2Topo_rsUpDownRuleOne_not_RqToUpRule:
    forall tr bidx oidx ridx msgId rqId prec trs ost orq ins,
      rule_precond (rsUpDownRuleOne ridx msgId rqId prec trs) ost orq ins ->
      ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rsUpDownRuleOne ridx msgId rqId prec trs).
  Proof.
    intros; intro.
    destruct H1.
    red in H1; dest.
    clear -H0 H3. (* [rule_precond] and [RqReleasing] *)
    specialize (H3 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H3 _ _ _ eq_refl).
    inv H3; discriminate.
  Qed.

  Lemma tree2Topo_rsUpUpRule_not_RqToUpRule:
    forall tr bidx oidx ridx msgId rqId prec trs ost orq ins,
      rule_precond (rsUpUpRule ridx msgId rqId prec trs) ost orq ins ->
      ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rsUpUpRule ridx msgId rqId prec trs).
  Proof.
    intros; intro.
    destruct H1.
    red in H1; dest.
    clear -H0 H3. (* [rule_precond] and [RqReleasing] *)
    specialize (H3 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H3 _ _ _ eq_refl).
    inv H3; discriminate.
  Qed.

  Lemma tree2Topo_rsUpUpRuleOne_not_RqToUpRule:
    forall tr bidx oidx ridx msgId rqId prec trs ost orq ins,
      rule_precond (rsUpUpRuleOne ridx msgId rqId prec trs) ost orq ins ->
      ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rsUpUpRuleOne ridx msgId rqId prec trs).
  Proof.
    intros; intro.
    destruct H1.
    red in H1; dest.
    clear -H0 H3. (* [rule_precond] and [RqReleasing] *)
    specialize (H3 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H3 _ _ _ eq_refl).
    inv H3; discriminate.
  Qed.

  Lemma tree2Topo_rsDownRqDownRule_not_RqToUpRule:
    forall tr bidx oidx ridx msgId rqId prec trs ost orq ins,
      rule_precond (rsDownRqDownRule ridx msgId oidx rqId prec trs) ost orq ins ->
      ~ RqToUpRule (fst (tree2Topo tr bidx)) oidx (rsDownRqDownRule ridx msgId oidx rqId prec trs).
  Proof.
    intros; intro.
    destruct H1.
    red in H2; dest.
    clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
    specialize (H5 _ _ _ H0).
    disc_rule_conds_ex.
    specialize (H5 _ _ _ eq_refl); dest.
    destruct H2.
    - dest; discriminate.
    - dest; disc_rule_conds_ex.
      destruct (fst (snd (trs ost msg idx))); [discriminate|].
      inv H4; apply rqEdgeUpFrom_rqUpFrom in H10; discriminate.
  Qed.

  Lemma tree2Topo_immRule_not_RsToUpRule:
    forall tr bidx oidx ridx prec trs ost orq ins,
      rule_precond (immRule ridx prec trs) ost orq ins ->
      ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (immRule ridx prec trs).
  Proof.
    intros; intro.
    destruct H1.
    - red in H1; dest.
      clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
      specialize (H5 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H5 _ _ _ eq_refl); dest; discriminate.
    - dest.
      red in H1; dest.
      red in H1.
      clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
      specialize (H1 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H1 _ _ _ eq_refl); dest; discriminate.
  Qed.

  Lemma tree2Topo_immDownRule_not_RsToUpRule:
    forall tr bidx cidx oidx ridx msgId prec trs ost orq ins,
      rule_precond (immDownRule ridx msgId cidx prec trs) ost orq ins ->
      ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (immDownRule ridx msgId cidx prec trs).
  Proof.
    intros; intro.
    destruct H1.
    - red in H1; dest.
      clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
      specialize (H5 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H5 _ _ _ eq_refl); dest.
      inv H5.
      apply rsEdgeUpFrom_rsUpFrom in H1; discriminate.
    - dest.
      red in H1; dest.
      red in H1.
      clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
      specialize (H1 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H1 _ _ _ eq_refl); dest; discriminate.
  Qed.

  Lemma tree2Topo_rqUpUpRule_not_RsToUpRule:
    forall tr bidx cidx oidx ridx msgId prec trs ost orq ins,
      rule_precond (rqUpUpRule ridx msgId cidx oidx prec trs) ost orq ins ->
      ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (rqUpUpRule ridx msgId cidx oidx prec trs).
  Proof.
    intros; intro.
    destruct H1.
    - red in H1; dest.
      clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
      specialize (H5 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H5 _ _ _ eq_refl); dest.
      inv H5.
      apply rsEdgeUpFrom_rsUpFrom in H1; discriminate.
    - dest.
      red in H1; dest.
      red in H1.
      clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
      specialize (H1 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H1 _ _ _ eq_refl); dest.
      apply f_equal with (f:= fun m => m@[upRq]) in H1; mred.
  Qed.

  Lemma tree2Topo_rqUpUpRuleS_not_RsToUpRule:
    forall tr bidx oidx ridx prec trs ost orq ins,
      rule_precond (rqUpUpRuleS ridx oidx prec trs) ost orq ins ->
      ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (rqUpUpRuleS ridx oidx prec trs).
  Proof.
    intros; intro.
    destruct H1.
    - red in H1; dest.
      clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
      specialize (H5 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H5 _ _ _ eq_refl); dest.
      destruct ins; discriminate.
    - dest.
      red in H1; dest.
      red in H1.
      clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
      specialize (H1 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H1 _ _ _ eq_refl); dest.
      unfold addRqS in H5.
      apply f_equal with (f:= fun m => m@[upRq]) in H5; mred.
  Qed.

  Lemma tree2Topo_rqUpDownRule_not_RsToUpRule:
    forall tr bidx cidx oidx ridx msgId prec trs ost orq ins,
      rule_precond (rqUpDownRule ridx msgId cidx oidx prec trs) ost orq ins ->
      ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (rqUpDownRule ridx msgId cidx oidx prec trs).
  Proof.
    intros; intro.
    destruct H1.
    - red in H1; dest.
      clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
      specialize (H5 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H5 _ _ _ eq_refl); dest.
      destruct (fst (trs ost rmsg)); [discriminate|].
      inv H5.
      apply rsEdgeUpFrom_rsUpFrom in H1; discriminate.
    - dest.
      red in H1; dest.
      red in H1.
      clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
      specialize (H1 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H1 _ _ _ eq_refl); dest.
      apply f_equal with (f:= fun m => m@[upRq]) in H1; mred.
  Qed.

  Lemma tree2Topo_rqDownDownRule_not_RsToUpRule:
    forall tr bidx oidx ridx msgId prec trs ost orq ins,
      rule_precond (rqDownDownRule ridx msgId oidx prec trs) ost orq ins ->
      ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (rqDownDownRule ridx msgId oidx prec trs).
  Proof.
    intros; intro.
    destruct H1.
    - red in H1; dest.
      clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
      specialize (H5 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H5 _ _ _ eq_refl); dest.
      destruct (fst (trs ost rmsg)); [discriminate|].
      inv H5.
      apply rsEdgeUpFrom_rsUpFrom in H1; discriminate.
    - dest.
      red in H1; dest.
      red in H1.
      clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
      specialize (H1 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H1 _ _ _ eq_refl); dest.
      apply f_equal with (f:= fun m => m@[upRq]) in H1; mred.
  Qed.

  Lemma tree2Topo_rsDownDownRule_not_RsToUpRule:
    forall tr bidx oidx ridx msgId rqId prec trs ost orq ins,
      rule_precond (rsDownDownRule ridx msgId rqId prec trs) ost orq ins ->
      ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (rsDownDownRule ridx msgId rqId prec trs).
  Proof.
    intros; intro.
    destruct H1.
    - red in H1; dest.
      red in H4.
      clear -H0 H4. (* [rule_precond] and [RulePostSat] *)
      specialize (H4 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H4 _ _ _ eq_refl); dest.
      apply f_equal with (f:= fun m => m@[upRq]) in H4; mred.
    - dest.
      red in H1; dest.
      red in H1.
      clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
      specialize (H1 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H1 _ _ _ eq_refl); dest.
      apply f_equal with (f:= fun m => m@[upRq]) in H3; mred.
  Qed.

  Lemma tree2Topo_rsDownDownRuleS_not_RsToUpRule:
    forall tr bidx oidx ridx msgId prec trs ost orq ins,
      rule_precond (rsDownDownRuleS ridx msgId prec trs) ost orq ins ->
      ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (rsDownDownRuleS ridx msgId prec trs).
  Proof.
    intros; intro.
    destruct H1.
    - red in H1; dest.
      red in H4.
      clear -H0 H4. (* [rule_precond] and [RulePostSat] *)
      specialize (H4 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H4 _ _ _ eq_refl); dest.
      apply f_equal with (f:= fun m => m@[upRq]) in H4; mred.
    - dest.
      red in H1; dest.
      red in H1.
      clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
      specialize (H1 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H1 _ _ _ eq_refl); dest.
      apply f_equal with (f:= fun m => m@[upRq]) in H4; mred.
  Qed.

  Lemma tree2Topo_rsDownRqDownRule_not_RsToUpRule:
    forall tr bidx oidx ridx msgId rqId prec trs ost orq ins,
      rule_precond (rsDownRqDownRule ridx msgId oidx rqId prec trs) ost orq ins ->
      ~ RsToUpRule (fst (tree2Topo tr bidx)) oidx (rsDownRqDownRule ridx msgId oidx rqId prec trs).
  Proof.
    intros; intro.
    destruct H1.
    - red in H1; dest.
      clear -H0 H5. (* [rule_precond] and [RulePostSat] *)
      specialize (H5 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H5 _ _ _ eq_refl); dest.
      destruct (fst (snd (trs ost msg idx))); [discriminate|].
      inv H8.
      apply rsEdgeUpFrom_rsUpFrom in H4; discriminate.
    - dest.
      red in H1; dest.
      red in H1.
      clear -H0 H1. (* [rule_precond] and [RulePostSat] *)
      specialize (H1 _ _ _ H0).
      disc_rule_conds_ex.
      specialize (H1 _ _ _ eq_refl); dest.
      apply f_equal with (f:= fun m => m@[upRq]) in H3; mred.
  Qed.

End DecValue.
