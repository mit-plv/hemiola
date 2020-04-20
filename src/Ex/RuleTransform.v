Require Import List FMap Omega.
Require Import Common Topology Syntax IndexSupport.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.TopoTemplate Ex.RuleTemplate.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Section RssHolder.
  Variable (dtr: DTree).
  Context `{dv:DecValue} `{oifc: OStateIfc}.

  Definition RsWaiting (cidx: IdxT): OPrec :=
    fun ost orq mins =>
      (orq@[downRq])
        >>=[False]
        (fun rqid => In (rsUpFrom cidx, None) rqid.(rqi_rss)).

  Definition RssFull: OPrec :=
    fun ost orq mins =>
      (orq@[downRq])
        >>=[False]
        (fun rqid => Forall (fun rs => snd rs <> None) rqid.(rqi_rss)).

  Fixpoint putRs (midx: IdxT) (msg: Msg) (rss: list (IdxT * option Msg)) :=
    match rss with
    | nil => nil
    | rs :: rss' =>
      if idx_dec midx (fst rs)
      then (midx, Some msg) :: rss'
      else rs :: (putRs midx msg rss')
    end.
  
  Definition addRs (orq: ORq Msg) (cidx: IdxT) (msg: Msg) :=
    (orq@[downRq])
      >>=[orq]
      (fun rqid => orq +[downRq <- {| rqi_msg := rqid.(rqi_msg);
                                      rqi_rss := putRs (rsUpFrom cidx) msg rqid.(rqi_rss);
                                      rqi_midx_rsb := rqid.(rqi_midx_rsb) |}]).

  Fixpoint retRss (rss: list (IdxT * option Msg)): list (Id Msg) :=
    match rss with
    | nil => nil
    | rs :: rss' =>
      match snd rs with
      | Some rsm => (fst rs, rsm) :: (retRss rss')
      | None => retRss rss'
      end
    end.
  
  Definition getRss (orq: ORq Msg) :=
    (orq@[downRq]) >>=[nil] (fun rqid => retRss rqid.(rqi_rss)).
  
  Variables
    (ridx msgId rqId: IdxT)
    (prec: OPrec).

  Variable (cidx: IdxT).

  Definition rsTakeOne :=
    rule[ridx]
    :requires (MsgsFrom [rsUpFrom cidx] /\ MsgIdsFrom [msgId] /\
               DownLockMsgId MRq rqId /\
               RsAccepting /\ RsWaiting cidx)
    :transition
       (do (st --> (msg <-- getFirstMsg st.(msgs);
                    return {{ st.(ost),
                              addRs st.(orq) (rsUpFrom cidx) msg,
                              nil }}))).

  Definition rsRelease (trs: OState ->
                             list (Id Msg) (* incoming messages *) ->
                             Msg (* the original request *) ->
                             IdxT (* response back to *) ->
                             OState * Miv) :=
    rule[ridx]
    :requires (MsgsFrom nil /\ DownLockMsgId MRq rqId /\
               RssFull /\ prec)
    :transition
       (do (st --> (rq <-- getDownLockMsg st.(orq);
                   rsbTo <-- getDownLockIdxBack st.(orq);
                   nst ::= trs st.(ost) (getRss st.(orq)) rq rsbTo;
                    return {{ fst nst,
                              removeRq st.(orq) downRq,
                              [(rsbTo, rsMsg (snd nst))] }}))).

  Definition rsReleaseOne (trs: OState ->
                                Id Msg (* incoming messages *) ->
                                Msg (* the original request *) ->
                                IdxT (* response back to *) ->
                                OState * Miv) :=
    rule[ridx]
    :requires (MsgsFrom nil /\ DownLockMsgId MRq rqId /\
               RssFull /\ prec)
    :transition
       (do (st --> (idm <-- getFirstIdMsg (getRss st.(orq));
                   rq <-- getDownLockMsg st.(orq);
                   rsbTo <-- getDownLockIdxBack st.(orq);
                   nst ::= trs st.(ost) idm rq rsbTo;
                    return {{ fst nst,
                              removeRq st.(orq) downRq,
                              [(rsbTo, rsMsg (snd nst))] }}))).

End RssHolder.

Notation "'rule.rsuo' '[' RIDX ']' ':accepts' MSGID ':holding' RQID ':from' FROM" :=
  (rsTakeOne RIDX MSGID RQID FROM) (at level 5).

Notation "'rule.rsr' '[' RIDX ']' ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsRelease RIDX RQID PREC TRS%trs) (at level 5).

Notation "'rule.rsro' '[' RIDX ']' ':holding' RQID ':requires' PREC ':transition' TRS" :=
  (rsReleaseOne RIDX RQID PREC TRS%trs) (at level 5).

