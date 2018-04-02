Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.
Require Import PredMsg.

Set Implicit Arguments.

Section GivenMsg.
  Variable (MsgT StateT: Type).
  Context `{HasMsg MsgT}.

  Definition toOrigMP (mp: MessagePool (PMsg MsgT)): MessagePool MsgT :=
    map (@pmsg_omsg _) mp.

  Inductive step_pred (psys: PSystem MsgT):
    @PState MsgT StateT -> PLabel MsgT ->
    @PState MsgT StateT -> Prop :=

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
      forall pst nst poss noss oidx pos nos otrss poims noims porig norig
             (immr: PRule MsgT) prec (rq: PMsg MsgT) (rs: PMsg MsgT),
        In oidx (indicesOf psys) ->
        In immr (psys_rules psys) ->
        immr = PRuleImm (pmsg_pmid rq) (pmsg_pmid rs) prec ->
        DualPMsg rq rs ->
        FirstMP poims rq ->
        ValidMsgsIn oidx (rq :: nil) ->

        poss@[oidx] = Some pos ->
        prec pos (getMsg rq :: nil) ->
        pred_os (pmsg_pred rq) (pmsg_val rq) poss (pmsg_val rs) noss ->
        pred_mp (pmsg_pred rq) (toOrigMP poims) (toOrigMP noims) ->

        noss = poss +[ oidx <- nos ] ->
        noims = distributeMsgs (intOuts psys (rs :: nil)) (removeMP rq poims) ->

        pst = {| pst_oss := poss; pst_otrss := otrss;
                 pst_msgs := poims; pst_orig := porig |} ->
        nst = {| pst_oss := noss; pst_otrss := otrss;
                 pst_msgs := noims; pst_orig := norig |} ->

        step_pred psys pst (PlblOuts (Some immr) (rq :: nil) (rs :: nil)) nst
                  
  | SpRqFwd:
      forall pst nst oss otrss oidx pos opred rsbf oims porig norig
             (rqfwdr: PRule MsgT) prec rqff
             (** TODO: need to know that [pmsg_omsg]s are 
              * related in terms of the original state transition rules.
              *)
             (rq: PMsg MsgT) (fwds: list (PMsg MsgT)),
        In oidx (indicesOf psys) ->
        In rqfwdr (psys_rules psys) ->
        rqfwdr = PRuleRqFwd (pmsg_pmid rq) prec opred rqff rsbf ->
        FirstMP oims rq ->
        ValidMsgsIn oidx (rq :: nil) ->
        ValidMsgOuts oidx fwds ->
        rqff (pmsg_pmid rq) = map (@pmsg_pmid _ _) fwds ->

        oss@[oidx] = Some pos ->
        prec pos (getMsg rq :: nil) ->

        pst = {| pst_oss := oss; pst_otrss := otrss;
                 pst_msgs := oims; pst_orig := porig |} ->
        nst = {| pst_oss := oss;
                 pst_otrss := otrss +[ oidx <- {| otrs_rq := rq;
                                                  otrs_opred := opred;
                                                  otrs_rsbf := rsbf |} ];
                 pst_msgs := distributeMsgs fwds (removeMP rq oims);
                 pst_orig := norig |} ->

        step_pred psys pst (PlblOuts (Some rqfwdr) (rq :: nil) fwds) nst

  | SpRsBack:
      forall pst nst oss otrss oidx pos nos otrs oims porig norig
             (rsbackr: PRule MsgT) (rss: list (PMsg MsgT)) (rsb: PMsg MsgT),
        In oidx (indicesOf psys) ->
        In rsbackr (psys_rules psys) ->
        rsbackr = PRuleRsBack (map (@pmsg_pmid _ _) rss) ->
        Forall (FirstMP oims) rss ->
        ValidMsgsIn oidx rss ->
        ValidMsgOuts oidx (rsb :: nil) ->

        oss@[oidx] = Some pos ->
        otrss@[oidx] = Some otrs ->

        Forall (fun pmsg =>
                  pred_os (pmsg_pred pmsg) (pmsg_val (otrs_rq otrs)) oss
                          (pmsg_val pmsg) (oss +[ oidx <- nos ]) /\
                  pred_mp (pmsg_pred pmsg) (toOrigMP oims)
                          (toOrigMP (enqMP rsb (removeMsgs rss oims)))) rss ->
        otrs_opred otrs (pmsg_val (otrs_rq otrs)) pos (pmsg_val rsb) nos ->
        DualPMsg (otrs_rq otrs) rsb ->
        pmsg_val rsb = otrs_rsbf otrs (map (fun pmsg => msg_value (getMsg pmsg)) rss) pos ->

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

