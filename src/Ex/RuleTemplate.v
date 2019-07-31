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
             (trs: OState -> Msg -> OState * Msg): Rule :=
    rule[ridx]
    :requires (MsgsFrom [rqUpFrom cidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ UpLockFree /\ DownLockFree /\ prec)
    :transition
       (do (msg <-- getFirstMsg;
              st --> let (ost, out) := trs (st.ost) msg in
                     (ost, st.orq, [(downTo cidx, out)]))).

  Definition immUpRule (oidx: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg -> OState * Msg): Rule :=
    rule[ridx]
    :requires (MsgsFrom [downTo oidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ DownLockFree /\ prec)
    :transition
       (do (msg <-- getFirstMsg;
              st --> let (ost, out) := trs (st.ost) msg in
                     (ost, st.orq, [(rqUpFrom oidx, out)]))).

  Definition rqUpUpRule (cidx oidx: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg -> Msg): Rule :=
    rule[ridx]
    :requires (MsgsFrom [rqUpFrom cidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ UpLockFree /\ prec)
    :transition
       (do (msg <-- getFirstMsg;
              st --> (st.ost,
                      addRq (st.orq) upRq msg [downTo oidx] (downTo cidx),
                      [(rqUpFrom oidx, trs (st.ost) msg)]))).

  Definition rqUpUpRuleS (oidx: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg): Rule :=
    rule[ridx]
    :requires (MsgsFrom nil /\ RqAccepting /\ UpLockFree /\ prec)
    :transition
       (fun ost orq _ =>
          (ost,
           addSilentUpRq orq [downTo oidx],
           [(rqUpFrom oidx, trs ost)])).

  (** * FIXME: need to know children indices from [trs] are sound. *)
  Definition rqUpDownRule (cidx oidx: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg -> list IdxT * Msg): Rule :=
    rule[ridx]
    :requires (MsgsFrom [rqUpFrom cidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ UpLockFree /\ DownLockFree /\ prec)
    :transition
       (do (msg <-- getFirstMsg;
              st --> let (cinds, out) := trs (st.ost) msg in
                     (st.ost,
                      addRq (st.orq) downRq msg (map rsUpFrom cinds) (downTo cidx),
                      map (fun cidx => (downTo cidx, msg)) cinds))).

  (** * FIXME: need to know children indices from [trs] are sound. *)
  Definition rqDownDownRule (oidx: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg -> list IdxT * Msg): Rule :=
    rule[ridx]
    :requires (MsgsFrom [downTo oidx] /\ MsgIdsFrom [msgId] /\
               RqAccepting /\ DownLockFree /\ prec)
    :transition
       (do (msg <-- getFirstMsg;
              st --> let (cinds, out) := trs (st.ost) msg in
                     (st.ost,
                      addRq (st.orq) downRq msg (map rsUpFrom cinds) (rsUpFrom oidx),
                      map (fun cidx => (downTo cidx, msg)) cinds))).

  Definition rsDownDownRule (rqId: IdxT)
             (prec: OPrec)
             (trs: OState ->
                   Msg (* an incoming message *) ->
                   Msg (* the original request *) ->
                   IdxT (* response back to *) ->
                   OState * Msg) :=
    rule[ridx]
    :requires (MsgsFromORq upRq /\ MsgIdsFrom [msgId] /\ UpLockMsgId MRq rqId /\
               RsAccepting /\ DownLockFree /\ prec)
    :transition
       (do (msg <-- getFirstMsg;
              rq <-- getUpLockMsg;
              rsbTo <-- getUpLockIdxBack;
              st --> let (ost, out) := trs (st.ost) msg rq rsbTo in
                     (ost, removeRq (st.orq) upRq, [(rsbTo, out)]))).

  Definition rsDownDownRuleS (rqId: IdxT)
             (prec: OPrec)
             (trs: OState ->
                   Msg (* an incoming message *) ->
                   Msg (* the original request *) ->
                   OState) :=
    rule[ridx]
    :requires (MsgsFromORq upRq /\ MsgIdsFrom [msgId] /\ UpLockMsgId MRq rqId /\
               RsAccepting /\ DownLockFree /\ prec)
    :transition
       (do (msg <-- getFirstMsg;
              rq <-- getUpLockMsg;
              rsbTo <-- getUpLockIdxBack;
              st --> (trs (st.ost) msg rq,
                      removeRq (st.orq) upRq,
                      nil))).

  Definition rsUpDownRule (rqId: IdxT)
             (prec: OPrec)
             (trs: OState ->
                   list (Id Msg) (* incoming messages *) ->
                   Msg (* the original request *) ->
                   list IdxT (* responses from *) ->
                   IdxT (* response back to *) ->
                   OState * Msg) :=
    rule[ridx]
    :requires (MsgsFromORq downRq /\ MsgIdFromEach msgId /\
               DownLockMsgId MRq rqId /\ RsAccepting /\ prec)
    :transition
       (do (rq <-- getDownLockMsg;
              rssFrom <-- getDownLockIndsFrom;
              rsbTo <-- getDownLockIdxBack;
              st --> let (ost, out) := trs (st.ost) (st.msgs) rq rssFrom rsbTo in
                     (ost,
                      removeRq (st.orq) downRq,
                      [(rsbTo, out)]))).

  Definition rsUpUpRule (rqId: IdxT)
             (prec: OPrec)
             (trs: OState ->
                   list (Id Msg) (* incoming messages *) ->
                   Msg (* the original request *) ->
                   list IdxT (* responses from *) ->
                   IdxT (* response back to *) ->
                   OState * Msg) :=
    rule[ridx]
    :requires (MsgsFromORq downRq /\ MsgIdFromEach msgId /\
               DownLockMsgId MRq rqId /\ RsAccepting /\ prec)
    :transition
       (do (rq <-- getDownLockMsg;
              rssFrom <-- getDownLockIndsFrom;
              rsbTo <-- getDownLockIdxBack;
              st --> let (ost, out) := trs (st.ost) (st.msgs) rq rssFrom rsbTo in
                     (ost,
                      removeRq (st.orq) downRq,
                      [(rsbTo, out)]))).

  (** * FIXME: need to know children indices from [trs] are sound. *)
  Definition rsDownRqDownRule (rqId: IdxT)
             (prec: OPrec)
             (trs: OState -> Msg -> list IdxT * Msg) :=
    rule[ridx]
    :requires (MsgsFromORq upRq /\ MsgIdsFrom [msgId] /\
               UpLockMsgId MRq rqId /\
               RsAccepting /\ DownLockFree /\ prec)
    :transition
       (do (rq <-- getUpLockMsg;
              rsbTo <-- getUpLockIdxBack;
              st --> let (cinds, out) := trs (st.ost) rq in
                     (st.ost,
                      addRq (removeRq (st.orq) upRq)
                            downRq rq (map rsUpFrom cinds) rsbTo,
                      map (fun cidx => (downTo cidx, out)) cinds))).
  
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

