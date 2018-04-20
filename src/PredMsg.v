Require Import Bool List String Peano_dec.
Require Import Common FMap.
Require Import Syntax Semantics.

Set Implicit Arguments.

Inductive RqRs := Rq | Rs.

Definition OPred :=
  Value (* input *) -> OState (* prestate *) ->
  Value (* output *) -> OState (* poststate *) -> Prop.

Definition PredOS :=
  Value (* input *) -> OStates (* prestate *) ->
  Value (* output *) -> OStates (* poststate *) -> Prop.

Definition PredMP (MsgT: Type) :=
  MessagePool MsgT (* prestate *) ->
  MessagePool MsgT (* poststate *) -> Prop.

Record Pred (MsgT: Type) :=
  { pred_os: PredOS;
    pred_mp: PredMP MsgT }.

Section GivenMsg.
  Variable (MsgT: Type).
  Context `{HasMsg MsgT}.

  Record PMsg :=
    { pmsg_omsg: MsgT;
      pmsg_pred: Pred MsgT }.

  Record PMsgId :=
    { pmid_mid: MsgId;
      pmid_pred: Pred MsgT }.

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
  Definition RsBackF := list Value -> OState -> Value.

  Inductive PRule :=
  | PRuleImm:
      forall (rq rs: PMsgId) (prec: RPrecond), PRule
  | PRuleRqFwd:
      forall (rq: PMsgId) (prec: RPrecond) (rqf: list PMsgId), PRule
  | PRuleRsBack:
      forall (rss: list PMsgId) (opred: OPred)
             (rsb: PMsgId) (rsbf: RsBackF), PRule.

  Definition oidxOfPRule (prule: PRule) :=
    match prule with
    | PRuleImm rq _ _ => mid_to (pmid_mid rq)
    | PRuleRqFwd rq _ _ => mid_to (pmid_mid rq)
    | PRuleRsBack _ _ rsb _ => mid_from (pmid_mid rsb)
    end.

  Definition midsOfPRule (prule: PRule) :=
    match prule with
    | PRuleImm rq _ _ => pmid_mid rq :: nil
    | PRuleRqFwd rq _ _ => pmid_mid rq :: nil
    | PRuleRsBack rss _ _ _ => map pmid_mid rss
    end.

  Definition precOfPRule (prule: PRule) :=
    match prule with
    | PRuleImm _ _ prec => prec
    | PRuleRqFwd _ prec _ => prec
    | PRuleRsBack _ _ _ _ => ⊤⊤
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

  Global Instance PSystem_OStates_HasInit: HasInit PSystem OStates :=
    {| initsOf := psys_inits |}.

  Record PState :=
    { pst_oss: OStates;
      pst_orqs: ORqs PMsg;
      pst_msgs: MessagePool PMsg
    }.

  Definition getPStateInit (psys: PSystem): PState :=
    {| pst_oss := initsOf psys;
       pst_orqs := [];
       pst_msgs := nil |}.

  Global Instance PState_PState_HasInit : HasInit PSystem PState :=
    {| initsOf := getPStateInit |}.

  (** Conversion from [PSystem] to [System] *)

  Definition pToRule (prule: PRule): Rule :=
    {| rule_oidx := oidxOfPRule prule; 
       rule_mids := midsOfPRule prule;
       (** TODO: how to convert? *)
       rule_precond := fun _ _ _ => True;
       rule_postcond := fun _ _ _ _ _ _ => True |}.

  Definition pToSystem (psys: PSystem): System :=
    {| sys_inds := psys_inds psys;
       sys_inits := psys_inits psys;
       sys_rules := map pToRule (psys_rules psys) |}.

End GivenMsg.

(** An instantiation with [TMsg] *)

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

Definition PTStateR (tst: TState) (pst: PState TMsg) :=
  tst_oss tst = pst_oss pst /\
  tst_orqs tst = M.map (map (@pmsg_omsg _)) (pst_orqs pst) /\
  tst_msgs tst = map (@pmsg_omsg _) (pst_msgs pst).

Section RuleAdder.
  Context {SysT: Type} `{IsSystem SysT} `{HasInit SysT OStates}.
  Variable (MsgT: Type).

  Definition buildRawPSys (osys: SysT): PSystem MsgT :=
    {| psys_inds := indicesOf osys;
       psys_inits := initsOf osys;
       psys_rules := nil |}.

  Definition addPRules (rules: list (PRule MsgT)) (sys: PSystem MsgT) :=
    {| psys_inds := psys_inds sys;
       psys_inits := psys_inits sys;
       psys_rules := psys_rules sys ++ rules |}.

End RuleAdder.

Fixpoint firstNonUnit (vs: list Value) :=
  match vs with
  | nil => VUnit
  | VUnit :: vs => firstNonUnit vs
  | v :: vs => v
  end.

Definition rsBackFDefault: RsBackF :=
  fun vs ost => firstNonUnit vs.

(* Instead of directly dealing with [rsBackFDefault], 
 * use reduction lemmas in [PredMsgFacts.v].
 *)
Global Opaque rsBackFDefault.

Definition PredMPTrue: PredMP TMsg :=
  fun _ _ => True.

Definition NoMsgsTs (ts: TrsId): PredMP TMsg :=
  fun pmsgs nmsgs =>
    ForallMP (fun tmsg =>
                (tmsg_info tmsg) >>=[True] (fun tinfo => tinfo_tid tinfo <> ts))
             nmsgs.

Section OStatesP.

  Definition OStatesP := OStates -> Prop.
  Definition OStateP := IdxT -> OState -> Prop.

  Definition OStatesFP := list IdxT -> OStatesP.
  Definition OStatesEP := IdxT -> OStatesP.

  Definition OStateForallP (ostp: OStateP): OStatesFP :=
    fun inds oss =>
      Forall (fun oidx =>
                oss@[oidx] >>=[False] (fun ost => ostp oidx ost)) inds.

  Definition OStateExistsP (ostp: OStateP): OStatesEP :=
    fun oidx oss =>
      exists ost,
        oss@[oidx] = Some ost /\ ostp oidx ost.

End OStatesP.

