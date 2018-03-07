Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.
Require Import PredMsg.

Set Implicit Arguments.

Inductive step_pred (psys: PSystem): PState -> PLabel -> PState -> Prop :=
| SpSlt: forall st, step_pred psys st emptyPLabel st

| SpExt:
    forall oss oims otrss (emsg: PMsg Rq),
      isExternal psys (mid_from (msg_id (getMsg emsg))) = true ->
      isInternal psys (mid_to (msg_id (getMsg emsg))) = true ->
      step_pred psys
                {| pst_oss := oss; pst_otrss := otrss; pst_msgs := oims |}
                (PlblIn emsg)
                {| pst_oss := oss;
                   pst_otrss := otrss;
                   pst_msgs := enqMP (existT _ _ emsg) oims
                |}

| SpImm:
    forall oss oidx pos nos otrss oims (immr: PRule) prec (rq: PMsg Rq) (rs: PMsg Rs),
      In oidx (indicesOf psys) ->
      In immr (psys_rules psys) ->
      immr = PRuleImm (pmsg_pmid rq) prec ->
      DualPMsg rq rs ->
      ValidMsgsIn oidx (rq :: nil) ->

      oss@[oidx] = Some pos ->
      prec pos (getMsg rq :: nil) ->
      (pmsg_pred rq) (pmsg_val rq) (oss +[ oidx <- nos ]) (pmsg_val rs) ->

      step_pred psys
                {| pst_oss := oss; pst_otrss := otrss; pst_msgs := oims |}
                (PlblOuts (Some immr)
                          (existT _ _ rq :: nil)
                          (existT _ _ rs :: nil))
                {| pst_oss := oss +[ oidx <- nos ];
                   pst_otrss := otrss;
                   pst_msgs := distributeMsgs
                                 (intOuts psys (existT _ _ rs :: nil))
                                 (removeMP (existT _ _ rq) oims)
                |}

| SpRqFwd:
    forall oss otrss oidx pos opred rsbf oims (rqfwdr: PRule) prec outf
           (rq: PMsg Rq) (fwds: list (PMsg Rq)) pred_ok,
      In oidx (indicesOf psys) ->
      In rqfwdr (psys_rules psys) ->
      rqfwdr = PRuleRqFwd (pmsg_pmid rq) prec outf ->
      ValidMsgsIn oidx (rq :: nil) ->
      ValidMsgOuts oidx fwds ->

      oss@[oidx] = Some pos ->
      prec pos (getMsg rq :: nil) ->

      step_pred psys
                {| pst_oss := oss; pst_otrss := otrss; pst_msgs := oims |}
                (PlblOuts (Some rqfwdr)
                          (existT _ _ rq :: nil)
                          (map (existT _ _) fwds))
                {| pst_oss := oss;
                   pst_otrss := otrss +[ oidx <- {| otrs_rq := rq;
                                                    otrs_opred := opred;
                                                    otrs_rsbf := rsbf;
                                                    otrs_pred_ok := pred_ok |} ];
                   pst_msgs := distributeMsgs
                                 (map (existT _ _) fwds)
                                 (removeMP (existT _ _ rq) oims)
                |}

| SpRsBack:
    forall oss otrss oidx pos nos otrs oims (rsbackr: PRule) rsbf
           (rss: list (PMsg Rs)) (rsb: PMsg Rs),
      In oidx (indicesOf psys) ->
      In rsbackr (psys_rules psys) ->
      rsbackr = PRuleRsBack (map (@pmsg_pmid _) rss) rsbf ->
      ValidMsgsIn oidx rss ->
      ValidMsgOuts oidx (rsb :: nil) ->

      oss@[oidx] = Some pos ->
      otrss@[oidx] = Some otrs ->

      Forall (fun pmsg => (pmsg_pred pmsg)
                            (pmsg_val (otrs_rq otrs)) oss (pmsg_val pmsg)) rss ->
      otrs_opred otrs (pmsg_val (otrs_rq otrs)) nos (pmsg_val rsb) ->
      otrs_rsbf otrs = rsbf ->
      DualPMsg (otrs_rq otrs) rsb ->
      pmsg_val rsb = rsbf (map getMsg rss) pos ->

      step_pred psys
                {| pst_oss := oss; pst_otrss := otrss; pst_msgs := oims |}
                (PlblOuts (Some rsbackr)
                          (map (existT _ _) rss)
                          (existT _ _ rsb :: nil))
                {| pst_oss := oss +[ oidx <- nos ];
                   pst_otrss := M.remove oidx otrss;
                   pst_msgs := enqMP (existT _ _ rsb)
                                     (removeMsgs (map (existT _ _) rss) oims)
                |}.

Definition steps_pred: Steps PSystem PState PLabel := steps step_pred.

