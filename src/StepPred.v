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

  | SpIns:
      forall pst nst oss oims orqs (eins: list (PMsg MsgT)),
        eins <> nil ->
        ValidMsgsExtIn psys eins ->
        pst = {| pst_oss := oss;
                 pst_orqs := orqs;
                 pst_msgs := oims |} ->
        nst = {| pst_oss := oss;
                 pst_orqs := orqs;
                 pst_msgs := distributeMsgs eins oims |} ->
        step_pred0 psys pst (PlblIns eins) nst

  | SpOuts:
      forall pst nst oss oims orqs (eouts: list (PMsg MsgT)),
        eouts <> nil ->
        ValidMsgsExtOut psys eouts ->
        pst = {| pst_oss := oss;
                 pst_orqs := orqs;
                 pst_msgs := oims |} ->
        nst = {| pst_oss := oss;
                 pst_orqs := orqs;
                 pst_msgs := removeMsgs eouts oims |} ->
        step_pred0 psys pst (PlblOuts eouts) nst

  | SpImm:
      forall pst nst poss noss oidx pos nos orqs porq poims noims
             (immr: PRule MsgT) prec (rq: PMsg MsgT) (rs: PMsg MsgT),
        In oidx (indicesOf psys) ->
        In immr (psys_rules psys) ->
        immr = PRuleImm (pmsg_pmid rq) (pmsg_pmid rs) prec ->
        DualPMsg rq rs ->
        FirstMP poims rq ->
        ValidMsgsIn oidx (rq :: nil) ->

        poss@[oidx] = Some pos ->
        orqs@[oidx] = Some porq ->
        prec pos (map (fun pmsg => getMsg (pmsg_omsg pmsg)) porq) (getMsg rq :: nil) ->
        pred_os (pmsg_pred rq) (pmsg_val rq) poss (pmsg_val rs) noss ->
        pred_mp (pmsg_pred rq) (toOrigMP poims) (toOrigMP noims) ->

        noss = poss +[ oidx <- nos ] ->
        noims = distributeMsgs (intOuts psys (rs :: nil)) (removeMP rq poims) ->

        pst = {| pst_oss := poss; pst_orqs := orqs; pst_msgs := poims |} ->
        nst = {| pst_oss := noss; pst_orqs := orqs; pst_msgs := noims |} ->

        step_pred0 psys pst (PlblInt (Some immr) (rq :: nil) (rs :: nil)) nst

  | SpRqFwd:
      forall pst nst oss porq orqs oidx pos oims
             (rqfwdr: PRule MsgT) prec
             (rq: PMsg MsgT) (fwds: list (PMsg MsgT)),
        In oidx (indicesOf psys) ->
        In rqfwdr (psys_rules psys) ->
        rqfwdr = PRuleRqFwd (pmsg_pmid rq) prec (map (@pmsg_pmid _ _) fwds) ->
        FirstMP oims rq ->
        ValidMsgsIn oidx (rq :: nil) ->
        ValidMsgsOut oidx fwds ->

        oss@[oidx] = Some pos ->
        prec pos (map (fun pmsg => getMsg (pmsg_omsg pmsg)) porq) (getMsg rq :: nil) ->

        orqs@[oidx] = Some porq ->

        pst = {| pst_oss := oss; pst_orqs := orqs; pst_msgs := oims |} ->
        nst = {| pst_oss := oss;
                 pst_orqs := orqs +[ oidx <- addRq porq rq ];
                 pst_msgs := distributeMsgs
                               (intOuts psys fwds)
                               (removeMP rq oims) |} ->

        step_pred0 psys pst (PlblInt (Some rqfwdr) (rq :: nil) fwds) nst

  | SpRsBack:
      forall pst nst oss orqs oidx pos nos orq origRq oims noss noims opred rsbf
             (rsbackr: PRule MsgT) (rss: list (PMsg MsgT)) (rsb: PMsg MsgT),
        In oidx (indicesOf psys) ->
        In rsbackr (psys_rules psys) ->
        rsbackr = PRuleRsBack (map (@pmsg_pmid _ _) rss) opred
                              (pmsg_pmid rsb) rsbf  ->
        Forall (FirstMP oims) rss ->
        ValidMsgsIn oidx rss ->
        ValidMsgsOut oidx (rsb :: nil) ->

        oss@[oidx] = Some pos ->
        orqs@[oidx] = Some orq ->
        getRq (fun pmsg => mid_tid (pmid_mid (pmsg_pmid pmsg)))
              orq (mid_tid (pmid_mid (pmsg_pmid rsb))) = Some origRq ->

        noss = oss +[ oidx <- nos ] ->
        noims = distributeMsgs
                  (intOuts psys (rsb :: nil))
                  (removeMsgs rss oims) ->
        
        (* Backing responses are all valid. *)
        Forall (fun pmsg =>
                  pred_os (pmsg_pred pmsg) (msg_value (getMsg (pmsg_omsg origRq))) oss
                          (pmsg_val pmsg) (oss +[ oidx <- nos ]) /\
                  pred_mp (pmsg_pred pmsg) (toOrigMP oims)
                          (toOrigMP (enqMP rsb (removeMsgs rss oims)))) rss ->
        opred (msg_value (getMsg (pmsg_omsg origRq))) pos (pmsg_val rsb) nos ->
        pmsg_val rsb = rsbf (map (fun pmsg => msg_value (getMsg pmsg)) rss) pos ->

        (* Using such responses, we should be able to prove 
         * the original request predicate.
         *)
        pred_os (pmsg_pred rsb) (msg_value (getMsg (pmsg_omsg origRq)))
                oss (pmsg_val rsb) noss ->
        pred_mp (pmsg_pred rsb) (toOrigMP oims) (toOrigMP noims) ->

        pst = {| pst_oss := oss;
                 pst_orqs := orqs;
                 pst_msgs := oims |} ->
        nst = {| pst_oss := noss;
                 pst_orqs := M.remove oidx orqs;
                 pst_msgs := noims |} ->

        step_pred0 psys pst (PlblInt (Some rsbackr) rss (rsb :: nil)) nst.

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

