Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.
Require Import PredMsg.

Set Implicit Arguments.

Section GivenMsg.
  Variable (MsgT StateT LabelT: Type).
  Context `{HasMsg MsgT} `{HasLabel LabelT}.

  Definition ResponsesOk (origRq: PMsg MsgT)
             (rss: list (PMsg MsgT)) (opred: OPred) (rsbf: RsBackF) :=
    forall poss noss post nost,
      Forall (fun rs =>
                (pred_os (pmsg_pred rs) (pmsg_val origRq) poss (pmsg_val rs) noss))
             rss ->
      poss@[mid_to (pmsg_mid origRq)] = Some post ->
      noss@[mid_to (pmsg_mid origRq)] = Some nost ->
      opred (pmsg_val origRq) post
            (rsbf (map (fun pmsg => msg_value (getMsg pmsg)) rss) nost) nost ->
      (pred_os (pmsg_pred origRq) (pmsg_val origRq) poss
               (rsbf (map (fun pmsg => msg_value (getMsg pmsg)) rss) nost)) noss.

  Definition toOrigMP (mp: MessagePool (PMsg MsgT)): MessagePool MsgT :=
    map (@pmsg_omsg _) mp.

  Inductive step_pred0 (psys: PSystem MsgT):
    PState MsgT -> PLabel MsgT -> PState MsgT -> Prop :=
  | SpSlt: forall st, step_pred0 psys st (emptyPLabel MsgT) st

  | SpExt:
      forall pst nst oss oims otrss (emsg: PMsg MsgT),
        fromExternal psys emsg = true ->
        toInternal psys emsg = true ->
        pst = {| pst_oss := oss;
                 pst_otrss := otrss;
                 pst_msgs := oims |} ->
        nst = {| pst_oss := oss;
                 pst_otrss := otrss;
                 pst_msgs := enqMP emsg oims |} ->
        step_pred0 psys pst (PlblIn emsg) nst

  | SpImm:
      forall pst nst poss noss oidx pos nos otrss poims noims
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

        pst = {| pst_oss := poss; pst_otrss := otrss; pst_msgs := poims |} ->
        nst = {| pst_oss := noss; pst_otrss := otrss; pst_msgs := noims |} ->

        step_pred0 psys pst (PlblOuts (Some immr) (rq :: nil) (rs :: nil)) nst

  | SpRqFwd:
      forall pst nst oss otrss oidx pos oims
             (rqfwdr: PRule MsgT) prec
             (rq: PMsg MsgT) (fwds: list (PMsg MsgT)),
        In oidx (indicesOf psys) ->
        In rqfwdr (psys_rules psys) ->
        rqfwdr = PRuleRqFwd (pmsg_pmid rq) prec (map (@pmsg_pmid _ _) fwds) ->
        FirstMP oims rq ->
        ValidMsgsIn oidx (rq :: nil) ->
        ValidMsgOuts oidx fwds ->

        oss@[oidx] = Some pos ->
        prec pos (getMsg rq :: nil) ->

        pst = {| pst_oss := oss; pst_otrss := otrss; pst_msgs := oims |} ->
        nst = {| pst_oss := oss;
                 pst_otrss := otrss +[ oidx <- {| otrs_rq := rq |} ];
                 pst_msgs := distributeMsgs fwds (removeMP rq oims) |} ->

        step_pred0 psys pst (PlblOuts (Some rqfwdr) (rq :: nil) fwds) nst

  | SpRsBack:
      forall pst nst oss otrss oidx pos nos otrs oims opred rsbf
             (rsbackr: PRule MsgT) (rss: list (PMsg MsgT)) (rsb: PMsg MsgT),
        In oidx (indicesOf psys) ->
        In rsbackr (psys_rules psys) ->
        rsbackr = PRuleRsBack (map (@pmsg_pmid _ _) rss) opred
                              (pmsg_pmid rsb) rsbf  ->
        Forall (FirstMP oims) rss ->
        ValidMsgsIn oidx rss ->
        ValidMsgOuts oidx (rsb :: nil) ->

        oss@[oidx] = Some pos ->
        otrss@[oidx] = Some otrs ->

        (* Backing responses are all valid. *)
        Forall (fun pmsg =>
                  pred_os (pmsg_pred pmsg) (pmsg_val (otrs_rq otrs)) oss
                          (pmsg_val pmsg) (oss +[ oidx <- nos ]) /\
                  pred_mp (pmsg_pred pmsg) (toOrigMP oims)
                          (toOrigMP (enqMP rsb (removeMsgs rss oims)))) rss ->
        opred (pmsg_val (otrs_rq otrs)) pos (pmsg_val rsb) nos ->
        pmsg_val rsb = rsbf (map (fun pmsg => msg_value (getMsg pmsg)) rss) pos ->

        (* Using such responses, we should be able to prove 
         * the original request predicate.
         *)
        DualPMsg (otrs_rq otrs) rsb ->
        ResponsesOk (otrs_rq otrs) rss opred rsbf ->

        pst = {| pst_oss := oss;
                 pst_otrss := otrss;
                 pst_msgs := oims |} ->
        nst = {| pst_oss := oss +[ oidx <- nos ];
                 pst_otrss := M.remove oidx otrss;
                 pst_msgs := enqMP rsb (removeMsgs rss oims) |} ->

        step_pred0 psys pst (PlblOuts (Some rsbackr) rss (rsb :: nil)) nst.

  Variables (SysT: Type)
            (ostep: Step SysT StateT LabelT)
            (sysF: PSystem MsgT -> SysT)
            (stR: StateT -> PState MsgT -> Prop)
            (lblF: PLabel MsgT -> LabelT).

  Record PStateEx :=
    { pstx_st: StateT;
      pstx_pst: PState MsgT;
      pstx_r: stR pstx_st pstx_pst
    }.

  Lemma PStateEx_ext:
    forall pstx1 pstx2,
      pstx_st pstx1 = pstx_st pstx2 ->
      pstx_pst pstx1 = pstx_pst pstx2 ->
      pstx1 = pstx2.
  Proof.
    destruct pstx1 as [st1 pst1 r1], pstx2 as [st2 pst2 r2].
    simpl; intros; subst.
    replace r1 with r2 by apply proof_irrelevance.
    reflexivity.
  Qed.

  Inductive step_pred (psys: PSystem MsgT):
    PStateEx -> PLabel MsgT -> PStateEx -> Prop :=
  | SpStep:
      forall pst nst plbl,
        ostep (sysF psys) (pstx_st pst) (lblF plbl) (pstx_st nst) ->
        step_pred0 psys (pstx_pst pst) plbl (pstx_pst nst) ->
        step_pred psys pst plbl nst.
  
End GivenMsg.

