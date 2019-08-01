Require Import List FMap Omega.
Require Import Common Topology Syntax IndexSupport.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.TopoTemplate.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Section Template.
  Variable (dtr: DTree).
  Context `{oifc: OStateIfc}.
  Variables (ridx msgId: IdxT).

  (* Heads-up: [cidx] is not the index of itself, but of a child. *)
  Definition immDownRule (cidx: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg -> option (OState * Msg)): Rule :=
    rule[ridx]
    :requires (MsgsFrom [rqUpFrom cidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ UpLockFree /\ DownLockFree /\ prec)
    :transition
       (do (st --> (msg <-- getFirstMsg st.(msgs);
                    nst <-- trs st.(ost) msg;
                    return {{ fst nst, st.(orq), [(downTo cidx, snd nst)] }}))).
  
  Definition immUpRule (oidx: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg -> option (OState * Msg)): Rule :=
    rule[ridx]
    :requires (MsgsFrom [downTo oidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ DownLockFree /\ prec)
    :transition
       (do (st --> (msg <-- getFirstMsg st.(msgs);
                      nst <-- trs st.(ost) msg;
                      return {{ fst nst, st.(orq), [(rqUpFrom oidx, snd nst)] }}))).

  Definition rqUpUpRule (cidx oidx: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg -> option Msg): Rule :=
    rule[ridx]
    :requires (MsgsFrom [rqUpFrom cidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ UpLockFree /\ prec)
    :transition
       (do (st --> (msg <-- getFirstMsg st.(msgs);
                      out <-- trs st.(ost) msg;
                      return {{ st.(ost),
                                addRq st.(orq) upRq msg [downTo oidx] (downTo cidx),
                                [(rqUpFrom oidx, out)] }}))).

  Definition rqUpUpRuleS (oidx: IdxT)
             (prec: OPrec)
             (trs: OState -> option Msg): Rule :=
    rule[ridx]
    :requires (MsgsFrom nil /\ RqAccepting /\ UpLockFree /\ prec)
    :transition
       (do (st --> (out <-- trs st.(ost);
                    return {{ st.(ost),
                              addSilentUpRq st.(orq) [downTo oidx],
                              [(rqUpFrom oidx, out)] }}))).

  (** * FIXME: need to know children indices from [trs] are sound. *)
  Definition rqUpDownRule (cidx oidx: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg -> option (list IdxT * Msg)): Rule :=
    rule[ridx]
    :requires (MsgsFrom [rqUpFrom cidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ UpLockFree /\ DownLockFree /\ prec)
    :transition
       (do (st -->
               (msg <-- getFirstMsg st.(msgs);
                  nst <-- trs st.(ost) msg;
                return {{ st.(ost),
                          addRq st.(orq) downRq msg
                                         (map rsUpFrom (fst nst)) (downTo cidx),
                          map (fun cidx => (downTo cidx, snd nst)) (fst nst) }}))).

  (** * FIXME: need to know children indices from [trs] are sound. *)
  Definition rqDownDownRule (oidx: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg -> option (list IdxT * Msg)): Rule :=
    rule[ridx]
    :requires (MsgsFrom [downTo oidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ DownLockFree /\ prec)
    :transition
       (do (st -->
               (msg <-- getFirstMsg st.(msgs);
                  nst <-- trs st.(ost) msg;
                return {{ st.(ost),
                          addRq st.(orq) downRq msg
                                         (map rsUpFrom (fst nst)) (rsUpFrom oidx),
                          map (fun cidx => (downTo cidx, snd nst)) (fst nst) }}))).

  Definition rsDownDownRule (rqId: IdxT)
             (prec: OPrec)
             (trs: OState ->
                   Msg (* an incoming message *) ->
                   Msg (* the original request *) ->
                   IdxT (* response back to *) ->
                   option (OState * Msg)) :=
    rule[ridx]
    :requires (MsgsFromORq upRq /\ MsgIdsFrom [msgId] /\ UpLockMsgId MRq rqId /\
               RsAccepting /\ DownLockFree /\ prec)
    :transition
       (do (st --> (msg <-- getFirstMsg st.(msgs);
                      rq <-- getUpLockMsg st.(orq);
                      rsbTo <-- getUpLockIdxBack st.(orq);
                      nst <-- trs st.(ost) msg rq rsbTo;
                    return {{ fst nst,
                              removeRq st.(orq) upRq,
                              [(rsbTo, snd nst)] }}))).

  Definition rsDownDownRuleS (rqId: IdxT)
             (prec: OPrec)
             (trs: OState ->
                   Msg (* an incoming message *) ->
                   Msg (* the original request *) ->
                   option OState) :=
    rule[ridx]
    :requires (MsgsFromORq upRq /\ MsgIdsFrom [msgId] /\ UpLockMsgId MRq rqId /\
               RsAccepting /\ DownLockFree /\ prec)
    :transition
       (do (st --> (msg <-- getFirstMsg st.(msgs);
                      rq <-- getUpLockMsg st.(orq);
                      rsbTo <-- getUpLockIdxBack st.(orq);
                      nst <-- trs st.(ost) msg rq;
                    return {{ nst, removeRq st.(orq) upRq, nil }}))).

  Definition rsUpDownRule (rqId: IdxT)
             (prec: OPrec)
             (trs: OState ->
                   list (Id Msg) (* incoming messages *) ->
                   Msg (* the original request *) ->
                   list IdxT (* responses from *) ->
                   IdxT (* response back to *) ->
                   option (OState * Msg)) :=
    rule[ridx]
    :requires (MsgsFromORq downRq /\ MsgIdFromEach msgId /\
               DownLockMsgId MRq rqId /\ RsAccepting /\ prec)
    :transition
       (do (st --> (rq <-- getDownLockMsg st.(orq);
                      rssFrom <-- getDownLockIndsFrom st.(orq);
                      rsbTo <-- getDownLockIdxBack st.(orq);
                      nst <-- trs st.(ost) st.(msgs) rq rssFrom rsbTo;
                    return {{ fst nst,
                              removeRq st.(orq) downRq,
                              [(rsbTo, snd nst)] }}))).

  Definition rsUpUpRule (rqId: IdxT)
             (prec: OPrec)
             (trs: OState ->
                   list (Id Msg) (* incoming messages *) ->
                   Msg (* the original request *) ->
                   list IdxT (* responses from *) ->
                   IdxT (* response back to *) ->
                   option (OState * Msg)) :=
    rule[ridx]
    :requires (MsgsFromORq downRq /\ MsgIdFromEach msgId /\
               DownLockMsgId MRq rqId /\ RsAccepting /\ prec)
    :transition
       (do (st --> (rq <-- getDownLockMsg st.(orq);
                      rssFrom <-- getDownLockIndsFrom st.(orq);
                      rsbTo <-- getDownLockIdxBack st.(orq);
                      nst <-- trs st.(ost) st.(msgs) rq rssFrom rsbTo;
                    return {{ fst nst,
                              removeRq st.(orq) downRq,
                              [(rsbTo, snd nst)] }}))).

  (** * FIXME: need to know children indices from [trs] are sound. *)
  Definition rsDownRqDownRule (rqId: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg -> option (list IdxT * Msg)) :=
    rule[ridx]
    :requires (MsgsFromORq upRq /\ MsgIdsFrom [msgId] /\
               UpLockMsgId MRq rqId /\
               RsAccepting /\ DownLockFree /\ prec)
    :transition
       (do (st --> (rq <-- getUpLockMsg st.(orq);
                      rsbTo <-- getUpLockIdxBack st.(orq);
                      nst <-- trs st.(ost) rq;
                    return {{ st.(ost),
                              addRq (removeRq st.(orq) upRq)
                                    downRq rq (map rsUpFrom (fst nst)) rsbTo,
                              map (fun cidx => (downTo cidx, snd nst))
                                  (fst nst) }}))).
  
End Template.

Notation "'rule.immd' '[' RIDX ']' ':accepts' MSGID ':from' FROM ':requires' PREC ':transition' TRS" :=
  (immDownRule RIDX MSGID FROM PREC%prec TRS%trs) (at level 5, only parsing).
Notation "'rule.immu' '[' RIDX ']' ':accepts' MSGID ':me' ME ':requires' PREC ':transition' TRS" :=
  (immUpRule RIDX MSGID ME PREC%prec TRS%trs) (at level 5).

Notation "'rule.rquu' '[' RIDX ']' ':accepts' MSGID ':from' FROM ':me' ME ':requires' PREC ':transition' TRS" :=
  (rqUpUpRule RIDX MSGID FROM ME PREC%prec TRS%trs) (at level 5).
Notation "'rule.rqu' '[' RIDX ']' ':me' ME ':requires' PREC ':transition' TRS" :=
  (rqUpUpRuleS RIDX ME PREC%prec TRS%trs) (at level 5).
Notation "'rule.rqud' '[' RIDX ']' ':accepts' MSGID ':from' FROM ':me' ME ':requires' PREC ':transition' TRS" :=
  (rqUpDownRule RIDX MSGID FROM ME PREC%prec TRS%trs) (at level 5).
Notation "'rule.rqdd' '[' RIDX ']' ':accepts' MSGID ':me' ME ':requires' PREC ':transition' TRS" :=
  (rqDownDownRule RIDX MSGID ME PREC%prec TRS%trs) (at level 5).

Notation "'rule.rsdd' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsDownDownRule RIDX MSGID RQID PREC%prec TRS%trs) (at level 5).
Notation "'rule.rsd' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsDownDownRuleS RIDX MSGID RQID PREC%prec TRS%trs) (at level 5).
Notation "'rule.rsud' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsUpDownRule RIDX MSGID RQID PREC%prec TRS%trs) (at level 5).
Notation "'rule.rsuu' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsUpUpRule RIDX MSGID RQID PREC%prec TRS%trs) (at level 5).

Notation "'rule.rsrq' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsDownRqDownRule RIDX MSGID RQID PREC%prec TRS%trs) (at level 5).

Section Facts.
  Variable (dtr: DTree).
  Context `{oifc: OStateIfc}.

  (* Lemma immDownRule_ImmDownRule: *)
  (*   forall oidx ridx msgId cidx prec trs, *)
  (*     parentIdxOf dtr cidx = Some oidx -> *)
  (*     ImmDownRule dtr oidx (immDownRule ridx msgId cidx prec trs). *)
  (* Proof. *)

End Facts.

