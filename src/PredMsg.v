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
Record PMsg (rr: RqRs) :=
  { pmsg_mid: MsgId;
    pmsg_val: Value;
    pmsg_pred: Pred }.

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

Inductive PRule: RqRs -> Type :=
| PRuleImm: forall (rq: MsgId) (prec: PRPrecond), PRule Rq
| PRuleRqFwd:
    forall (rq: MsgId) (prec: PRPrecond)
           (fwds: PMsg Rq -> OState -> list (PMsg Rq)), PRule Rq
| PRuleRsBack:
    forall (rss: list MsgId) (prec: PRPrecond)
           (rsb: list (PMsg Rs) -> OState -> PMsg Rs), PRule Rs.

Definition PRuleSig := { rr : RqRs & PRule rr }.

(* Record PRule := *)
(*   { rule_mids: list MsgId; *)
(*     rule_precond: PRPrecond; *)
(*     rule_outs: PROuts }. *)

Section PLabel.

  Inductive PLabel :=
  | PlblIn {rr} (min: PMsg rr): PLabel
  | PlblOuts (hdl: option { rr : RqRs & PRule rr })
             (mins: list PMsgSig) (mouts: list PMsgSig): PLabel.

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
    psys_rules: list PRuleSig }.

Record OTrs :=
  { otrs_rqval: Value;
    otrs_pred: Pred;
    otrs_opred: OPred;
    otrs_rsb: list Value -> OState -> Value }.

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
    forall oss oidx pos nos otrss oims (immr: PRule Rq) prec (rq: PMsg Rq) (rs: PMsg Rs),
      In oidx (indicesOf psys) ->
      In (existT _ _ immr) (psys_rules psys) ->
      immr = PRuleImm (msg_id (getMsg rq)) prec ->
      DualPMsg rq rs ->
      ValidMsgsIn oidx (rq :: nil) ->

      oss@[oidx] = Some pos ->
      prec pos (getMsg rq :: nil) ->
      PredOk (pmsg_pred rq) (pmsg_val rq) (oss +[ oidx <- nos ]) (pmsg_val rs) ->

      step_pred psys
                {| pst_oss := oss; pst_otrss := otrss; pst_msgs := oims |}
                (PlblOuts (Some (existT _ _ immr))
                          (existT _ _ rq :: nil)
                          (existT _ _ rs :: nil))
                {| pst_oss := oss +[ oidx <- nos ];
                   pst_otrss := otrss;
                   pst_msgs := distributeMsgs
                                 (intOuts psys (existT _ _ rs :: nil))
                                 (removeMP (existT _ _ rq) oims)
                |}

| SRqFwd:
    forall oss otrss (* oidx *) (* otrs *) oims (rqfwdr: PRule Rq) prec outf
           (rq: PMsg Rq) (fwds: list (PMsg Rq)),
      rqfwdr = PRuleRqFwd (msg_id (getMsg rq)) prec outf ->

      (* TODOs: conditions *)

      step_pred psys
                {| pst_oss := oss; pst_otrss := otrss; pst_msgs := oims |}
                (PlblOuts (Some (existT _ _ rqfwdr))
                          (existT _ _ rq :: nil)
                          (map (existT _ _) fwds))
                {| pst_oss := oss;
                   pst_otrss := otrss; (* TODO: otrss +[ oidx <- ... ] *)
                   pst_msgs := distributeMsgs
                                 (map (existT _ _) fwds)
                                 (removeMP (existT _ _ rq) oims)
                |}.

