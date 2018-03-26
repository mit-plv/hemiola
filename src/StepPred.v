Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.
Require Import PredMsg.

Set Implicit Arguments.

Section GivenMsg.
  Variable (MsgT StateT: Type).
  Context `{HasMsg MsgT}.

  Inductive step_pred (psys: PSystem MsgT):
    @PState MsgT _ StateT -> PLabel MsgT ->
    @PState MsgT _ StateT -> Prop :=

  | SpSlt: forall st, step_pred psys st (emptyPLabel MsgT) st

  | SpExt:
      forall pst nst oss oims porig norig otrss (emsg: PMsg MsgT),
        fromExternal psys emsg = true ->
        toInternal psys emsg = true ->
        pst = {| pst_oss := oss;
                 pst_otrss := otrss;
                 pst_msgs := oims;
                 pst_orig := porig |} ->
        nst = {| pst_oss := oss;
                 pst_otrss := otrss;
                 pst_msgs := enqMP emsg oims;
                 pst_orig := norig |} ->
        step_pred psys pst (PlblIn emsg) nst

  | SpImm:
      forall pst nst oss oidx pos nos otrss oims porig norig
             (immr: PRule MsgT) prec (rq: PMsg MsgT) (rs: PMsg MsgT),
        In oidx (indicesOf psys) ->
        In immr (psys_rules psys) ->
        immr = PRuleImm _ (pmsg_pmid rq) (pmsg_pmid rs) prec ->
        DualPMsg rq rs ->
        FirstMP oims rq ->
        ValidMsgsIn oidx (rq :: nil) ->

        oss@[oidx] = Some pos ->
        prec pos (getMsg rq :: nil) ->
        (pmsg_pred rq) (pmsg_val rq) oss (pmsg_val rs) (oss +[ oidx <- nos ]) ->

        pst = {| pst_oss := oss;
                 pst_otrss := otrss;
                 pst_msgs := oims;
                 pst_orig := porig |} ->
        nst = {| pst_oss := oss +[ oidx <- nos ];
                 pst_otrss := otrss;
                 pst_msgs := distributeMsgs
                               (intOuts psys (rs :: nil))
                               (removeMP rq oims);
                 pst_orig := norig |} ->

        step_pred psys pst (PlblOuts (Some immr) (rq :: nil) (rs :: nil)) nst
                  
  | SpRqFwd:
      forall pst nst oss otrss oidx pos opred rsbf oims porig norig
             (rqfwdr: PRule MsgT) prec outf
             (rq: PMsg MsgT) (fwds: list (PMsg MsgT)) pred_ok,
        In oidx (indicesOf psys) ->
        In rqfwdr (psys_rules psys) ->
        rqfwdr = PRuleRqFwd (pmsg_pmid rq) prec outf ->
        FirstMP oims rq ->
        ValidMsgsIn oidx (rq :: nil) ->
        ValidMsgOuts oidx fwds ->

        oss@[oidx] = Some pos ->
        prec pos (getMsg rq :: nil) ->

        pst = {| pst_oss := oss;
                 pst_otrss := otrss;
                 pst_msgs := oims;
                 pst_orig := porig |} ->
        nst = {| pst_oss := oss;
                 pst_otrss := otrss +[ oidx <- {| otrs_rq := rq;
                                                  otrs_opred := opred;
                                                  otrs_rsbf := rsbf;
                                                  otrs_pred_ok := pred_ok |} ];
                 pst_msgs := distributeMsgs fwds (removeMP rq oims);
                 pst_orig := norig |} ->

        step_pred psys pst (PlblOuts (Some rqfwdr) (rq :: nil) fwds) nst

  | SpRsBack:
      forall pst nst oss otrss oidx pos nos otrs oims porig norig
             (rsbackr: PRule MsgT) rsbf
             (rss: list (PMsg MsgT)) (rsb: PMsg MsgT),
        In oidx (indicesOf psys) ->
        In rsbackr (psys_rules psys) ->
        rsbackr = PRuleRsBack _ (map (@pmsg_pmid _ _) rss) rsbf ->
        Forall (FirstMP oims) rss ->
        ValidMsgsIn oidx rss ->
        ValidMsgOuts oidx (rsb :: nil) ->

        oss@[oidx] = Some pos ->
        otrss@[oidx] = Some otrs ->

        Forall (fun pmsg => (pmsg_pred pmsg)
                              (pmsg_val (otrs_rq otrs)) oss
                              (pmsg_val pmsg) (oss +[ oidx <- nos ])) rss ->
        otrs_opred otrs (pmsg_val (otrs_rq otrs)) pos (pmsg_val rsb) nos ->
        otrs_rsbf otrs = rsbf ->
        DualPMsg (otrs_rq otrs) rsb ->
        pmsg_val rsb = rsbf (map getMsg rss) pos ->

        pst = {| pst_oss := oss;
                 pst_otrss := otrss;
                 pst_msgs := oims;
                 pst_orig := porig |} ->
        nst = {| pst_oss := oss +[ oidx <- nos ];
                 pst_otrss := M.remove oidx otrss;
                 pst_msgs := enqMP rsb (removeMsgs rss oims);
                 pst_orig := norig |} ->

        step_pred psys pst (PlblOuts (Some rsbackr) rss (rsb :: nil)) nst.

End GivenMsg.

