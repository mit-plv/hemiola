Require Import Bool List String Peano_dec.
Require Import Common FMap.
Require Import Syntax Semantics.

Set Implicit Arguments.

Inductive RqRs := Rq | Rs.

Definition OPred :=
  Value (* input *) -> OState -> Value (* output *) -> Prop.

Definition Pred :=
  Value (* input *) -> OStates -> Value (* output *) -> Prop.

Record PMsgId :=
  { pmid_mid: MsgId;
    pmid_pred: Pred }.

Record PMsg (rr: RqRs) :=
  { pmsg_pmid: PMsgId;
    pmsg_val: Value }.

Definition pmsg_mid {rr} (pmsg: PMsg rr) := pmid_mid (pmsg_pmid pmsg).
Definition pmsg_pred {rr} (pmsg: PMsg rr) := pmid_pred (pmsg_pmid pmsg).

(* No conditions about [mid_chn]; it's only about liveness. *)
Definition DualMid (rq rs: MsgId) :=
  mid_tid rq = mid_tid rs /\
  mid_from rq = mid_to rs /\
  mid_to rq = mid_from rs.

Definition DualPMsg (rq: PMsg Rq) (rs: PMsg Rs) :=
  DualMid (pmsg_mid rq) (pmsg_mid rs) /\
  pmsg_pred rq = pmsg_pred rs.

Definition dualOf (mid: MsgId) (dchn: IdxT) :=
  {| mid_addr := {| ma_from := ma_to (mid_addr mid);
                    ma_to := ma_from (mid_addr mid);
                    ma_chn := dchn |};
     mid_tid := mid_tid mid |}.

Definition dualOfP (pmid: PMsgId) (dchn: IdxT) :=
  {| pmid_mid := dualOf (pmid_mid pmid) dchn;
     pmid_pred := pmid_pred pmid |}.

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

Definition RqFwdF := PMsg Rq -> OState -> list (PMsg Rq).
Definition RsBackF := list Msg -> OState -> Value.

Inductive PRule :=
| PRuleImm: forall (rq rs: PMsgId) (prec: PRPrecond), PRule
| PRuleRqFwd: forall (rq: PMsgId) (prec: PRPrecond) (fwds: RqFwdF), PRule
| PRuleRsBack: forall (rss: list PMsgId) (rsbf: RsBackF), PRule.

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

Definition PHistory := list PLabel.

Record PSystem :=
  { psys_inds: list IdxT;
    psys_inits: OStates;
    psys_rules: list PRule }.

Definition ForwardingOk (rq: PMsg Rq) (opred: OPred) (rsbf: RsBackF) :=
  forall oss ost rss,
    Forall (fun rs: PMsg Rs =>
              (pmsg_pred rs) (pmsg_val rq) oss (pmsg_val rs)) rss ->
    oss@[mid_to (pmsg_mid rq)] = Some ost ->
    opred (pmsg_val rq) ost (rsbf (map getMsg rss) ost) ->
    (pmsg_pred rq) (pmsg_val rq) oss (rsbf (map getMsg rss) ost).

Record OTrs :=
  { otrs_rq: PMsg Rq;
    otrs_opred: OPred;
    otrs_rsbf: RsBackF;
    otrs_pred_ok: ForwardingOk otrs_rq otrs_opred otrs_rsbf
  }.

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

Definition pToTMsg (ts: TrsId) (rqin: Msg) (pmsg: PMsgSig): TMsg :=
  {| tmsg_msg := {| msg_id := pmsg_mid (projT2 pmsg);
                    msg_value := pmsg_val (projT2 pmsg)
                 |};
     tmsg_info := Some {| tinfo_tid := ts; tinfo_rqin := rqin :: nil |}
  |}.

Definition pToTState (ts: TrsId) (rqin: Msg) (pst: PState): TState :=
  {| tst_oss := pst_oss pst;
     tst_msgs := map (pToTMsg ts rqin) (pst_msgs pst);
     tst_tid := ts |}.

Definition pToTLabel (ts: TrsId) (rqin: Msg) (plbl: PLabel): TLabel :=
  match plbl with
  | PlblIn min => RlblIn (pToTMsg ts rqin (existT _ _ min))
  | PlblOuts oprule mins mouts =>
    RlblOuts (lift pToRule oprule)
             (map (pToTMsg ts rqin) mins)
             (map (pToTMsg ts rqin) mouts)
  end.

Definition pToTHistory (ts: TrsId) (rqin: Msg) (phst: PHistory): THistory :=
  map (pToTLabel ts rqin) phst.

Section RuleAdder.
  Context {SysT: Type} `{IsSystem SysT OStates}.

  Definition buildRawPSys (osys: SysT) :=
    {| psys_inds := indicesOf osys;
       psys_inits := initsOf osys;
       psys_rules := nil |}.

  Definition addPRules (rules: list PRule) (sys: PSystem) :=
    {| psys_inds := psys_inds sys;
       psys_inits := psys_inits sys;
       psys_rules := psys_rules sys ++ rules |}.

End RuleAdder.

