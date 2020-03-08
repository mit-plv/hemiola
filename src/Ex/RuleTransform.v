Require Import List FMap Omega.
Require Import Common Topology Syntax IndexSupport.
Require Import RqRsLang. Import RqRsNotations.

Require Import Ex.TopoTemplate Ex.RuleTemplate.

Set Implicit Arguments.

Local Open Scope list.
Local Open Scope fmap.

Section Transform.
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
  
  Section RssHolder.

    Variables
      (ridx msgId rqId: IdxT)
      (prec: OPrec)
      (trs: OState ->
            list (Id Msg) (* incoming messages *) ->
            Msg (* the original request *) ->
            IdxT (* response back to *) ->
            OState * Miv).

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

    Definition rsRelease :=
      rule[ridx]
      :requires (MsgsFrom nil (* /\ DownLockMsgId MRq rqId *) (** required? *) /\
                 RssFull /\ prec)
      :transition
         (do (st --> (rq <-- getDownLockMsg st.(orq);
                      rsbTo <-- getDownLockIdxBack st.(orq);
                      nst ::= trs st.(ost) (getRss st.(orq)) rq rsbTo;
                      return {{ fst nst,
                                removeRq st.(orq) downRq,
                                [(rsbTo, rsMsg (snd nst))] }}))).

  End RssHolder.

End Transform.

