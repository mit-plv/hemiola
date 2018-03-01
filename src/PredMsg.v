Require Import Bool List String Peano_dec.
Require Import Common FMap.
Require Import Syntax Semantics.

Set Implicit Arguments.

Inductive RqRs := Rq | Rs.

Definition OPred :=
  Value (* input *) -> OState -> Value (* output *) -> Prop.

Definition Pred := M.t OPred.

Definition PredOk (pred: Pred) (rqv: Value) (oss: OStates) (rsv: Value) :=
  forall oidx,
    pred@[oidx] >>=[True]
        (fun opred =>
           oss@[oidx] >>=[False] (fun ost => opred rqv ost rsv)).

(* Need to check if [pmsg_val] can be removed, to make [pmsg_pred] have enough
 * information instead.
 *)

Record PMsgId :=
  { pmid_mid: MsgId;
    pmid_pred: Pred }.

Record PMsg (rr: RqRs) :=
  { pmsg_pmid: PMsgId;
    pmsg_val: Value }.

Definition pmsg_mid {rr} (pmsg: PMsg rr) := pmid_mid (pmsg_pmid pmsg).
Definition pmsg_pred {rr} (pmsg: PMsg rr) := pmid_pred (pmsg_pmid pmsg).

(* From the perspective of correctness, [mid_chn] is only about liveness. *)
Definition DualMid (rq rs: MsgId) :=
  mid_tid rq = mid_tid rs /\
  mid_from rq = mid_to rs /\
  mid_to rq = mid_from rs.

Definition DualPMsg (rq: PMsg Rq) (rs: PMsg Rs) :=
  DualMid (pmsg_mid rq) (pmsg_mid rs) /\
  pmsg_pred rq = pmsg_pred rs.

Definition PMsgSig := { rr : RqRs & PMsg rr }.

Definition msgOfPMsg {rr} (pmsg: PMsg rr) :=
  buildMsg (pmsg_mid pmsg) (pmsg_val pmsg).

Global Instance PMsg_HasMsg (rr: RqRs): HasMsg (PMsg rr) :=
  {| getMsg := msgOfPMsg |}.

Global Instance PMsgSig_HasMsg : HasMsg PMsgSig :=
  {| getMsg := fun pmsg => msgOfPMsg (projT2 pmsg) |}.

(* Note that a precondition of [PRule] is nothing to do with predicates of
 * input [PMsg]s. Even if the same [PMsg]s are requested, different transitions
 * are required wrt. different situations (preconditions).
 *)
Definition PRPrecond := OState -> list Msg -> Prop.
Definition PROuts := list PMsgSig -> OState -> list PMsgSig.

Inductive PRule :=
| PRuleImm: forall (rq: PMsgId) (prec: PRPrecond), PRule 
| PRuleRqFwd:
    forall (rq: PMsgId) (prec: PRPrecond)
           (fwds: PMsg Rq -> OState -> list (PMsg Rq)), PRule
| PRuleRsBack:
    forall (rss: list PMsgId) (rsbf: list Msg -> OState -> Value), PRule.

(* Record PRule := *)
(*   { rule_mids: list PMsgId; *)
(*     rule_precond: PRPrecond; *)
(*     rule_outs: PROuts }. *)

Section PLabel.

  Inductive PLabel :=
  | PlblIn {rr} (min: PMsg rr): PLabel
  | PlblOuts (hdl: option PRule) (mins: list PMsgSig) (mouts: list PMsgSig): PLabel.

  Definition pLblIns (l: PLabel) :=
    match l with
    | PlblIn _ => nil
    | PlblOuts _ mins _ => mins
    end.

  Definition pLblOuts (l: PLabel) :=
    match l with
    | PlblIn _ => nil
    | PlblOuts _ _ mouts => mouts
    end.

  Definition pToLabel (l: PLabel): Label :=
    match l with
    | PlblIn min => LblIn (getMsg min)
    | PlblOuts _ _ mouts => LblOuts (map getMsg mouts)
    end.

  Global Instance PLabel_HasLabel: HasLabel PLabel :=
    { getLabel := pToLabel }.

  Definition emptyPLabel := PlblOuts None nil nil.

End PLabel.

Record PSystem :=
  { psys_inds: list IdxT;
    psys_inits: OStates;
    psys_rules: list PRule }.

Record OTrs :=
  { otrs_rq: PMsg Rq;
    otrs_opred: OPred }.

Record PState :=
  { pst_oss: OStates;
    pst_otrss: M.t OTrs;
    pst_msgs: MessagePool PMsgSig
  }.

Global Instance PSystem_OStates_IsSystem : IsSystem PSystem OStates :=
  {| indicesOf := psys_inds;
     initsOf := psys_inits |}.

Definition getPStateInit (psys: PSystem): PState :=
  {| pst_oss := initsOf psys;
     pst_otrss := [];
     pst_msgs := nil |}.

Global Instance PSystem_PState_IsSystem : IsSystem PSystem PState :=
  {| indicesOf := psys_inds;
     initsOf := getPStateInit |}.

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
      PredOk (pmsg_pred rq) (pmsg_val rq) (oss +[ oidx <- nos ]) (pmsg_val rs) ->

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

| SRqFwd:
    forall oss otrss oidx pos notrs oims (rqfwdr: PRule) prec outf
           (rq: PMsg Rq) (fwds: list (PMsg Rq)),
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
                   pst_otrss := otrss +[ oidx <- notrs ];
                   pst_msgs := distributeMsgs
                                 (map (existT _ _) fwds)
                                 (removeMP (existT _ _ rq) oims)
                |}

| SRsBack:
    forall oss otrss oidx pos nos otrs oims (rsbackr: PRule) rsbf
           (rss: list (PMsg Rs)) (rsb: PMsg Rs),
      In oidx (indicesOf psys) ->
      In rsbackr (psys_rules psys) ->
      rsbackr = PRuleRsBack (map (@pmsg_pmid _) rss) rsbf ->
      ValidMsgsIn oidx rss ->
      ValidMsgOuts oidx (rsb :: nil) ->

      oss@[oidx] = Some pos ->
      otrss@[oidx] = Some otrs ->

      (* All predicates in the response messages are satisfied. *)
      Forall (fun pmsg => PredOk (pmsg_pred pmsg)
                                 (pmsg_val (otrs_rq otrs)) oss (pmsg_val pmsg)) rss ->
      otrs_opred otrs (pmsg_val (otrs_rq otrs)) nos (pmsg_val rsb) ->

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

(**
 * Informal TODOs:
 * 1) To prove [steps_det -> Transactional -> steps_pred]
 * 2) To check [steps_pred] is indeed useful for syntheses.
 *)

