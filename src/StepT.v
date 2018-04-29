Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepM.

Fixpoint getTMsgsTInfo (tmsgs: list TMsg) :=
  match tmsgs with
  | nil => None
  | tmsg :: tmsgs' =>
    match tmsg_info tmsg with
    | Some ti => Some ti
    | None => getTMsgsTInfo tmsgs'
    end
  end.

Inductive step_t (sys: System): TState -> TLabel -> TState -> Prop :=
| StSlt: forall st, step_t sys st (emptyRLabel _) st
| StIns: forall ts pst nst oss orqs msgs eins,
    eins <> nil ->
    ValidMsgsExtIn sys eins ->
    pst = {| tst_oss := oss; tst_orqs := orqs; tst_msgs := msgs; tst_tid := ts |} ->
    nst = {| tst_oss := oss;
             tst_orqs := orqs;
             tst_msgs := distributeMsgs (toTMsgsU eins) msgs;
             tst_tid := ts
          |} ->
    step_t sys pst (RlblIns (toTMsgsU eins)) nst
| StOuts: forall ts pst nst oss orqs msgs eouts,
    eouts <> nil ->
    Forall (FirstMP msgs) eouts ->
    ValidMsgsExtOut sys eouts ->
    pst = {| tst_oss := oss; tst_orqs := orqs; tst_msgs := msgs; tst_tid := ts |} ->
    nst = {| tst_oss := oss;
             tst_orqs := orqs;
             tst_msgs := removeMsgs eouts msgs;
             tst_tid := ts
          |} ->
    step_t sys pst (RlblOuts eouts) nst
| StInt: forall ts pst nst nts (Hts: nts > ts) tinfo
                oss orqs msgs oidx os porq pos norq ins rule outs,
    oidx = rule_oidx rule ->
    In oidx (indicesOf sys) ->
    oss@[oidx] = Some os ->
    orqs@[oidx] = Some porq ->
    Forall (FirstMP msgs) ins ->
    ValidMsgsIn oidx ins ->
    map (fun tmsg => msg_id (tmsg_msg tmsg)) ins = rule_mids rule ->
    In rule (sys_rules sys) ->
    rule_precond rule os (map tmsg_msg porq) (map tmsg_msg ins) ->
    rule_postcond rule os (map tmsg_msg porq) (map tmsg_msg ins)
                  pos (map tmsg_msg norq) outs ->
    ValidMsgsOut oidx outs ->

    tinfo = match getTMsgsTInfo ins with
            | Some ti => ti
            | None => {| tinfo_tid := nts; tinfo_rqin := map tmsg_msg ins |}
            end ->

    pst = {| tst_oss := oss; tst_orqs := orqs; tst_msgs := msgs; tst_tid := ts |} ->
    nst = {| tst_oss := oss +[ oidx <- pos ];
             tst_orqs := orqs +[ oidx <- norq ];
             tst_msgs := distributeMsgs (toTMsgs tinfo outs) (removeMsgs ins msgs);
             tst_tid := match getTMsgsTInfo ins with
                        | Some _ => ts
                        | None => nts
                        end
          |} ->

    step_t sys pst (RlblInt (Some rule) ins (toTMsgs tinfo outs)) nst.

Definition TORqsRel (torqs: ORqs TMsg) (orqs: ORqs Msg) :=
  forall oidx,
    match torqs@[oidx], orqs@[oidx] with
    | Some torq, Some orq => map tmsg_msg torq = orq
    | None, None => True
    | _, _ => False
    end.

Definition TMsgsRel (tmsgs: MessagePool TMsg) (msgs: MessagePool Msg) :=
  map tmsg_msg tmsgs = msgs.

Definition TStateRel (tst: TState) (st: MState) :=
  tst_oss tst = bst_oss st /\
  TORqsRel (tst_orqs tst) (bst_orqs st) /\
  TMsgsRel (tst_msgs tst) (bst_msgs st).

Definition tToMLabel (tlbl: TLabel) :=
  match tlbl with
  | RlblIns eins => RlblIns (map tmsg_msg eins)
  | RlblOuts eouts => RlblOuts (map tmsg_msg eouts)
  | RlblInt orule mins mouts =>
    RlblInt orule (map tmsg_msg mins) (map tmsg_msg mouts)
  end.

