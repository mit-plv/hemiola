Require Import Bool List String Peano_dec.
Require Import Common FMap.
Require Import Syntax Semantics.

Set Implicit Arguments.

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
    { pmid_midx: IdxT;
      pmid_msg_id: IdxT;
      pmid_pred: Pred MsgT }.

  Definition pmsg_mid (pmsg: PMsg) := msg_id (getMsg (pmsg_omsg pmsg)).
  Definition pmsg_val (pmsg: PMsg) := msg_value (getMsg (pmsg_omsg pmsg)).

  Definition pmidOf (idp: Id PMsg) :=
    {| pmid_midx := idOf idp;
       pmid_msg_id := pmsg_mid (valOf idp);
       pmid_pred := pmsg_pred (valOf idp) |}.

  Global Instance PMsg_HasMsg: HasMsg PMsg :=
    {| getMsg := fun pmsg => getMsg (pmsg_omsg pmsg) |}.

  (* Note that a precondition of [PRule] is nothing to do with predicates of
   * input [PMsg]s. Even if the same [PMsg]s are requested, different transitions
   * are required wrt. different situations (preconditions).
   *)
  Definition RsBackF := list Value -> OState -> Value.

  Inductive PRule :=
  | PRuleImm:
      forall (oidx: IdxT) (rq rs: PMsgId) (prec: RPrecond), PRule
  | PRuleRqFwd:
      forall (oidx: IdxT) (rq: PMsgId) (prec: RPrecond) (rqf: list PMsgId), PRule
  | PRuleRsBack:
      forall (oidx: IdxT) (rss: list PMsgId) (opred: OPred)
             (rsb: PMsgId) (rsbf: RsBackF), PRule.

  Definition oidxOfPRule (prule: PRule) :=
    match prule with
    | PRuleImm oidx _ _ _ => oidx
    | PRuleRqFwd oidx _ _ _ => oidx
    | PRuleRsBack oidx _ _ _ _ => oidx
    end.

  Definition mindsOfPRule (prule: PRule) :=
    match prule with
    | PRuleImm _ rq _ _ => pmid_midx rq :: nil
    | PRuleRqFwd _ rq _ _ => pmid_midx rq :: nil
    | PRuleRsBack _ rss _ _ _ => map pmid_midx rss
    end.

  Definition msgIdsOfPRule (prule: PRule) :=
    match prule with
    | PRuleImm _ rq _ _ => pmid_msg_id rq :: nil
    | PRuleRqFwd _ rq _ _ => pmid_msg_id rq :: nil
    | PRuleRsBack _ rss _ _ _ => map pmid_msg_id rss
    end.

  Definition precOfPRule (prule: PRule) :=
    match prule with
    | PRuleImm _ _ _ prec => prec
    | PRuleRqFwd _ _ prec _ => prec
    | PRuleRsBack _ _ _ _ _ => ⊤rprec
    end.

  Section PLabel.

    Inductive PLabel :=
    | PlblEmpty
    | PlblIns (mins: list (Id PMsg)): PLabel
    | PlblInt (hdl: PRule) (mins: list (Id PMsg)) (mouts: list (Id PMsg)): PLabel
    | PlblOuts (mouts: list (Id PMsg)): PLabel.
 
    Definition pToLabel (l: PLabel): option Label :=
      match l with
      | PlblEmpty => None
      | PlblIns mins => Some (LblIns (imap getMsg mins))
      | PlblInt _ _ _ => None
      | PlblOuts mouts => Some (LblOuts (imap getMsg mouts))
      end.

    Global Instance PLabel_HasLabel: HasLabel PLabel :=
      { getLabel := pToLabel }.

  End PLabel.

  Definition PHistory := list PLabel.

  Record PSystem :=
    { psys_oinds: list IdxT;
      psys_minds: list IdxT;
      psys_merqs: list IdxT;
      psys_merss: list IdxT;
      psys_msg_inds_valid: NoDup (psys_minds ++ psys_merqs ++ psys_merss);
      psys_inits: OStates;
      psys_rules: list PRule }.

  Global Instance PSystem_IsSystem: IsSystem PSystem :=
    {| oindsOf := psys_oinds;
       mindsOf := psys_minds;
       merqsOf := psys_merqs;
       merssOf := psys_merss;
       msg_inds_valid := psys_msg_inds_valid
    |}.

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
       pst_msgs := [] |}.

  Global Instance PState_PState_HasInit : HasInit PSystem PState :=
    {| initsOf := getPStateInit |}.

  (** Conversion from [PSystem] to [System] *)

  Definition pToRule (prule: PRule): Rule :=
    {| rule_oidx := oidxOfPRule prule; 
       rule_minds := mindsOfPRule prule;
       rule_msg_ids := msgIdsOfPRule prule;
       (** TODO: how to convert? *)
       rule_precond := fun _ _ _ => True;
       rule_postcond := fun _ _ _ _ _ _ => True |}.

  Definition pToSystem (psys: PSystem): System :=
    {| sys_oinds := psys_oinds psys;
       sys_minds := psys_minds psys;
       sys_merqs := psys_merqs psys;
       sys_merss := psys_merss psys;
       sys_msg_inds_valid := psys_msg_inds_valid psys;
       sys_inits := psys_inits psys;
       sys_rules := map pToRule (psys_rules psys) |}.

End GivenMsg.

(** An instantiation with [TMsg] *)

Definition pToTLabel (plbl: PLabel TMsg): TLabel :=
  match plbl with
  | PlblEmpty _ => RlblEmpty _
  | PlblIns mins => RlblIns (imap (@pmsg_omsg _) mins)
  | PlblInt oprule mins mouts =>
    RlblInt (pToRule oprule) (imap (@pmsg_omsg _) mins) (imap (@pmsg_omsg _) mouts)
  | PlblOuts mouts => RlblOuts (imap (@pmsg_omsg _) mouts)
  end.

Definition pToTHistory (phst: PHistory TMsg): THistory :=
  map pToTLabel phst.

Definition PTStateR (tst: TState) (pst: PState TMsg) :=
  tst_oss tst = pst_oss pst /\
  tst_orqs tst = M.map (orqMap (@pmsg_omsg _)) (pst_orqs pst) /\
  tst_msgs tst = M.map (map (@pmsg_omsg _)) (pst_msgs pst).

Section RuleAdder.
  Context {SysT: Type} `{IsSystem SysT} `{HasInit SysT OStates}.
  Variable (MsgT: Type).

  Definition buildRawPSys (osys: SysT): PSystem MsgT :=
    {| psys_oinds := oindsOf osys;
       psys_minds := mindsOf osys;
       psys_merqs := merqsOf osys;
       psys_merss := merssOf osys;
       psys_msg_inds_valid := msg_inds_valid osys;
       psys_inits := initsOf osys;
       psys_rules := nil |}.

  Definition addPRules (rules: list (PRule MsgT)) (sys: PSystem MsgT) :=
    {| psys_oinds := psys_oinds sys;
       psys_minds := psys_minds sys;
       psys_merqs := psys_merqs sys;
       psys_merss := psys_merss sys;
       psys_msg_inds_valid := psys_msg_inds_valid sys;
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

(** TODO: check whether we really need this predicate. *)
Definition NoMsgsTs (ts: TrsId): PredMP TMsg :=
  fun pmsgs nmsgs =>
    ForallMP (fun _ tmsg =>
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

