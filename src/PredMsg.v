Require Import Bool List String Peano_dec.
Require Import Common FMap.
Require Import Syntax Semantics.

Set Implicit Arguments.

Inductive RqRs := Rq | Rs.

Definition OPred :=
  Value (* input *) -> OState (* prestate *) ->
  Value (* output *) -> OState (* poststate *) -> Prop.

Definition Pred :=
  Value (* input *) -> OStates (* prestate *) ->
  Value (* output *) -> OStates (* poststate *) -> Prop.

Section GivenMsg.
  Variable (MsgT: Type).
  Context `{HasMsg MsgT}.

  Record PMsg :=
    { pmsg_omsg: MsgT;
      pmsg_pred: Pred }.

  Record PMsgId :=
    { pmid_mid: MsgId;
      pmid_pred: Pred }.

  Definition pmsg_mid (pmsg: PMsg) := msg_id (getMsg (pmsg_omsg pmsg)).
  Definition pmsg_val (pmsg: PMsg) := msg_value (getMsg (pmsg_omsg pmsg)).

  Definition pmsg_pmid (pmsg: PMsg) :=
    {| pmid_mid := pmsg_mid pmsg;
       pmid_pred := pmsg_pred pmsg |}.

  Definition DualPMsgId (rq rs: PMsgId) :=
    DualMid (pmid_mid rq) (pmid_mid rs) /\
    pmid_pred rq = pmid_pred rs.

  Definition DualPMsg (rq rs: PMsg) :=
    DualMid (pmsg_mid rq) (pmsg_mid rs) /\
    pmsg_pred rq = pmsg_pred rs.

  Definition dualOfP (pmid: PMsgId) (dchn: IdxT) :=
    {| pmid_mid := dualOf (pmid_mid pmid) dchn;
       pmid_pred := pmid_pred pmid |}.

  Global Instance PMsg_HasMsg: HasMsg PMsg :=
    {| getMsg := fun pmsg => getMsg (pmsg_omsg pmsg) |}.

  (* Note that a precondition of [PRule] is nothing to do with predicates of
   * input [PMsg]s. Even if the same [PMsg]s are requested, different transitions
   * are required wrt. different situations (preconditions).
   *)
  Definition PRPrecond := OState -> list Msg -> Prop.
  Definition PROuts := list PMsg -> OState -> list PMsg.

  Definition RqFwdF := PMsg -> OState -> list PMsg.
  Definition RsBackF := list Msg -> OState -> Value.

  Inductive PRule :=
  | PRuleImm:
      forall (rq rs: PMsgId) (prec: PRPrecond), PRule
  | PRuleRqFwd:
      forall (rq: PMsgId) (prec: PRPrecond) (fwds: RqFwdF), PRule
  | PRuleRsBack:
      forall (rss: list PMsgId) (rsbf: RsBackF), PRule.

  Definition midsOfPRule (prule: PRule) :=
    match prule with
    | PRuleImm rq _ _ => pmid_mid rq :: nil
    | PRuleRqFwd rq _ _ => pmid_mid rq :: nil
    | PRuleRsBack rss _ => map pmid_mid rss
    end.

  Definition precOfPRule (prule: PRule) :=
    match prule with
    | PRuleImm _ _ prec => prec
    | PRuleRqFwd _ prec _ => prec
    | PRuleRsBack _ _ => ⊤
    end.

  Section PLabel.

    Inductive PLabel :=
    | PlblIn (min: PMsg): PLabel
    | PlblOuts (hdl: option PRule) (mins: list PMsg) (mouts: list PMsg): PLabel.

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

  Definition PHistory := list PLabel.

  Record PSystem :=
    { psys_inds: list IdxT;
      psys_inits: OStates;
      psys_rules: list PRule }.

  Global Instance PSystem_IsSystem: IsSystem PSystem :=
    {| indicesOf := psys_inds |}.

  Definition ForwardingOk (rq: PMsg) (opred: OPred) (rsbf: RsBackF) :=
    forall poss noss post nost rss,
      Forall (fun rs =>
                (pmsg_pred rs) (pmsg_val rq) poss (pmsg_val rs) noss)
             rss ->
      poss@[mid_to (pmsg_mid rq)] = Some post ->
      noss@[mid_to (pmsg_mid rq)] = Some nost ->
      opred (pmsg_val rq) post (rsbf (map getMsg rss) nost) nost ->
      (pmsg_pred rq) (pmsg_val rq) poss (rsbf (map getMsg rss) nost) noss.

  Record OTrs :=
    { otrs_rq: PMsg;
      otrs_opred: OPred;
      otrs_rsbf: RsBackF;
      otrs_pred_ok: ForwardingOk otrs_rq otrs_opred otrs_rsbf
    }.

  Section GivenState.
    Variable (StateT: Type).
    Context `{HasInit StateT}.

    Record PState :=
      { pst_oss: OStates;
        pst_otrss: M.t OTrs;
        pst_msgs: MessagePool PMsg;
        pst_orig: StateT
      }.

    Definition getPStateInit: PState :=
      {| pst_oss := initsOf;
         pst_otrss := [];
         pst_msgs := nil;
         pst_orig := initsOf |}.

    Global Instance PState_HasInit : HasInit PState :=
      {| initsOf := getPStateInit |}.

    (** Conversion from [PSystem] to [System] *)

    Definition pToRule (prule: PRule): Rule :=
      {| rule_mids := midsOfPRule prule;
         rule_precond := precOfPRule prule;
         (** * TODO: how to convert? *)
         rule_postcond := ⊤⊤⊤ |}.

    Definition pToSystem (psys: PSystem): System :=
      {| sys_inds := psys_inds psys;
         sys_inits := psys_inits psys;
         sys_rules := map pToRule (psys_rules psys) |}.

  End GivenState.

End GivenMsg.

Definition PTMsg := PMsg TMsg.
Definition PTState := @PState TMsg _ TState.

Definition pToTState (pst: PTState): TState :=
  {| tst_oss := pst_oss pst;
     tst_msgs := map (@pmsg_omsg _) (pst_msgs pst);
     tst_tid := tst_tid (pst_orig pst) |}.

Definition pToTLabel (plbl: PLabel TMsg): TLabel :=
  match plbl with
  | PlblIn min => RlblIn (pmsg_omsg min)
  | PlblOuts oprule mins mouts =>
    RlblOuts (lift (@pToRule TMsg) oprule)
             (map (@pmsg_omsg _) mins)
             (map (@pmsg_omsg _) mouts)
  end.

Definition pToTHistory (phst: PHistory TMsg): THistory :=
  map pToTLabel phst.

Section RuleAdder.
  Context {SysT: Type} `{IsSystem SysT}.
  Variable (MsgT: Type).

  Definition buildRawPSys (osys: SysT): PSystem MsgT :=
    {| psys_inds := indicesOf osys;
       psys_inits := initsOf;
       psys_rules := nil |}.

  Definition addPRules (rules: list (PRule MsgT)) (sys: PSystem MsgT) :=
    {| psys_inds := psys_inds sys;
       psys_inits := psys_inits sys;
       psys_rules := psys_rules sys ++ rules |}.

End RuleAdder.

