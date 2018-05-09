Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.
Require Import PredMsg.

Set Implicit Arguments.

Section GivenMsg.
  Variable (MsgT StateT LabelT: Type).
  Context `{HasMsg MsgT} `{HasLabel LabelT}.

  Definition toOrigMP {MsgT} := mpmap (@pmsg_omsg MsgT).

  Inductive step_pred0 (psys: PSystem MsgT):
    PState MsgT -> PLabel MsgT -> PState MsgT -> Prop :=
  | SpSlt: forall st, step_pred0 psys st (emptyPLabel MsgT) st

  | SpIns:
      forall pst nst oss oims orqs (eins: list (Id (PMsg MsgT))),
        eins <> nil ->
        ValidMsgsExtIn psys eins ->
        pst = {| pst_oss := oss;
                 pst_orqs := orqs;
                 pst_msgs := oims |} ->
        nst = {| pst_oss := oss;
                 pst_orqs := orqs;
                 pst_msgs := enqMsgs eins oims |} ->
        step_pred0 psys pst (PlblIns eins) nst

  | SpOuts:
      forall pst nst oss oims orqs (eouts: list (Id (PMsg MsgT))),
        eouts <> nil ->
        ValidMsgsExtOut psys eouts ->
        pst = {| pst_oss := oss;
                 pst_orqs := orqs;
                 pst_msgs := oims |} ->
        nst = {| pst_oss := oss;
                 pst_orqs := orqs;
                 pst_msgs := deqMsgs (idsOf eouts) oims |} ->
        step_pred0 psys pst (PlblOuts eouts) nst

  | SpImm:
      forall pst nst poss noss oidx pos nos orqs porq poims noims
             (immr: PRule MsgT) prec (rq: Id (PMsg MsgT)) (rs: Id (PMsg MsgT)),
        In oidx (oindsOf psys) ->
        In immr (psys_rules psys) ->
        immr = PRuleImm oidx (pmidOf rq) (pmidOf rs) prec ->
        (* DualPMsg rq rs -> *)
        FirstMPI poims rq ->
        ValidMsgsIn psys (rq :: nil) ->

        poss@[oidx] = Some pos ->
        orqs@[oidx] = Some porq ->
        prec pos (imap (fun pmsg => getMsg (pmsg_omsg pmsg)) porq)
             (liftI getMsg rq :: nil) ->
        pred_os (pmsg_pred (valOf rq)) (pmsg_val (valOf rq)) poss
                (pmsg_val (valOf rs)) noss ->
        pred_mp (pmsg_pred (valOf rq)) (toOrigMP poims) (toOrigMP noims) ->

        noss = poss +[ oidx <- nos ] ->
        noims = enqMPI rq (deqMP (idOf rq) poims) ->

        pst = {| pst_oss := poss; pst_orqs := orqs; pst_msgs := poims |} ->
        nst = {| pst_oss := noss; pst_orqs := orqs; pst_msgs := noims |} ->

        step_pred0 psys pst (PlblInt (Some immr) (rq :: nil) (rs :: nil)) nst

  | SpRqFwd:
      forall pst nst oss porq orqs oidx pos oims
             (rqfwdr: PRule MsgT) prec
             (rq: Id (PMsg MsgT)) (fwds: list (Id (PMsg MsgT))),
        In oidx (oindsOf psys) ->
        In rqfwdr (psys_rules psys) ->
        rqfwdr = PRuleRqFwd oidx (pmidOf rq) prec (map (@pmidOf _ _) fwds) ->
        FirstMPI oims rq ->
        ValidMsgsIn psys (rq :: nil) ->
        ValidMsgsOut psys fwds ->

        oss@[oidx] = Some pos ->
        prec pos (imap (fun pmsg => getMsg (pmsg_omsg pmsg)) porq)
             (liftI getMsg rq :: nil) ->

        orqs@[oidx] = Some porq ->

        pst = {| pst_oss := oss; pst_orqs := orqs; pst_msgs := oims |} ->
        nst = {| pst_oss := oss;
                 pst_orqs := orqs +[ oidx <- addRq porq rq ];
                 pst_msgs := enqMsgs fwds (deqMP (idOf rq) oims) |} ->

        step_pred0 psys pst (PlblInt (Some rqfwdr) (rq :: nil) fwds) nst

  | SpRsBack:
      forall pst nst oss orqs oidx pos nos orq origRq oims noss noims opred rsbf
             (rsbackr: PRule MsgT)
             (rss: list (Id (PMsg MsgT))) (rsb: Id (PMsg MsgT)),
        In oidx (oindsOf psys) ->
        In rsbackr (psys_rules psys) ->
        rsbackr = PRuleRsBack oidx (map (@pmidOf _ _) rss)
                              opred (pmidOf rsb) rsbf  ->
        Forall (FirstMPI oims) rss ->
        ValidMsgsIn psys rss ->
        ValidMsgsOut psys (rsb :: nil) ->

        oss@[oidx] = Some pos ->
        orqs@[oidx] = Some orq ->
        getRq orq (idOf rsb) = Some origRq ->

        noss = oss +[ oidx <- nos ] ->
        noims = enqMsgs (rsb :: nil) (deqMsgs (idsOf rss) oims) ->
        
        (* Backing responses are all valid. *)
        Forall (fun pmsg =>
                  pred_os (pmsg_pred pmsg) (msg_value (getMsg (pmsg_omsg (valOf origRq))))
                          oss (pmsg_val pmsg) (oss +[ oidx <- nos ]) /\
                  pred_mp (pmsg_pred pmsg) (toOrigMP oims)
                          (toOrigMP (enqMPI rsb (deqMsgs (idsOf rss) oims))))
               (valsOf rss) ->
        opred (msg_value (getMsg (pmsg_omsg (valOf origRq)))) pos (pmsg_val (valOf rsb)) nos ->
        pmsg_val (valOf rsb) = rsbf (map (fun idp => msg_value (getMsg (valOf idp))) rss) pos ->

        (* Using such responses, we should be able to prove 
         * the original request predicate.
         *)
        pred_os (pmsg_pred (valOf rsb)) (msg_value (getMsg (pmsg_omsg (valOf origRq))))
                oss (pmsg_val (valOf rsb)) noss ->
        pred_mp (pmsg_pred (valOf rsb)) (toOrigMP oims) (toOrigMP noims) ->

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

