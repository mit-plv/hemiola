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
| PRuleImm: forall (rq: PMsgId) (prec: PRPrecond), PRule
| PRuleRqFwd: forall (rq: PMsgId) (prec: PRPrecond) (fwds: RqFwdF), PRule
| PRuleRsBack: forall (rss: list PMsgId) (rsbf: RsBackF), PRule.

Definition midsOfPRule (prule: PRule) :=
  match prule with
  | PRuleImm rq _ => pmid_mid rq :: nil
  | PRuleRqFwd rq _ _ => pmid_mid rq :: nil
  | PRuleRsBack rss _ => map pmid_mid rss
  end.

Definition precOfPRule (prule: PRule) :=
  match prule with
  | PRuleImm _ prec => prec
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
              PredOk (pmsg_pred rs) (pmsg_val rq) oss (pmsg_val rs)) rss ->
    oss@[mid_to (pmsg_mid rq)] = Some ost ->
    opred (pmsg_val rq) ost (rsbf (map getMsg rss) ost) ->
    PredOk (pmsg_pred rq) (pmsg_val rq) oss (rsbf (map getMsg rss) ost).

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

