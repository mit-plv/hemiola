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
| StIns: forall ts pst nst oss orqs msgs trss eins,
    eins <> nil ->
    ValidMsgsExtIn sys eins ->
    pst = {| tst_oss := oss; tst_orqs := orqs;
             tst_msgs := msgs; tst_trss := trss; tst_tid := ts |} ->
    nst = {| tst_oss := oss; tst_orqs := orqs;
             tst_msgs := enqMsgs (imap toTMsgU eins) msgs;
             tst_trss := enqMsgs (imap toTMsgU eins) trss;
             tst_tid := ts
          |} ->
    step_t sys pst (RlblIns (imap toTMsgU eins)) nst
| StOuts: forall ts pst nst oss orqs msgs trss eouts,
    eouts <> nil ->
    Forall (fun idm => FirstMP (fst idm) (snd idm) msgs) eouts ->
    ValidMsgsExtOut sys eouts ->
    pst = {| tst_oss := oss; tst_orqs := orqs;
             tst_msgs := msgs; tst_trss := trss; tst_tid := ts |} ->
    nst = {| tst_oss := oss;
             tst_orqs := orqs;
             tst_msgs := deqMsgs (idsOf eouts) msgs;
             tst_trss := deqMsgs (idsOf eouts) trss;
             tst_tid := ts
          |} ->
    step_t sys pst (RlblOuts eouts) nst
| StInt: forall ts pst nst nts (Hts: nts > ts) tinfo
                oss orqs msgs trss oidx os porq pos norq ins rule outs,
    oidx = rule_oidx rule ->
    In oidx (oindsOf sys) ->
    oss@[oidx] = Some os ->
    orqs@[oidx] = Some porq ->
    
    Forall (fun idm => FirstMP (fst idm) (snd idm) msgs) ins ->
    ValidMsgsIn sys ins ->
    idsOf ins = rule_minds rule ->
    
    In rule (sys_rules sys) ->
    rule_precond rule os (map tmsg_msg porq) (imap tmsg_msg ins) ->
    rule_postcond rule os (map tmsg_msg porq) (imap tmsg_msg ins)
                  pos (map tmsg_msg norq) outs ->
    ValidMsgsOut outs ->

    tinfo = match getTMsgsTInfo (valsOf ins) with
            | Some ti => ti
            | None => {| tinfo_tid := nts;
                         tinfo_rqin := imap tmsg_msg ins |}
            end ->

    pst = {| tst_oss := oss; tst_orqs := orqs;
             tst_msgs := msgs; tst_trss := trss; tst_tid := ts |} ->
    nst = {| tst_oss := oss +[ oidx <- pos ];
             tst_orqs := orqs +[ oidx <- norq ];
             tst_msgs := enqMsgs (imap (toTMsg tinfo) outs)
                                 (deqMsgs (idsOf ins) msgs);
             tst_trss := trss; (* FIXME *)
             tst_tid := match getTMsgsTInfo (valsOf ins) with
                        | Some _ => ts
                        | None => nts
                        end
          |} ->

    step_t sys pst (RlblInt (Some rule) ins (imap (toTMsg tinfo) outs)) nst.

Definition TORqsRel (torqs: ORqs TMsg) (orqs: ORqs Msg) :=
  forall oidx,
    match torqs@[oidx], orqs@[oidx] with
    | Some torq, Some orq => map tmsg_msg torq = orq
    | None, None => True
    | _, _ => False
    end.

Definition TMsgsRel (tmsgs: MessagePool TMsg) (msgs: MessagePool Msg) :=
  forall midx,
    map tmsg_msg (findQ midx tmsgs) = findQ midx msgs.

Definition TStateRel (tst: TState) (st: MState) :=
  tst_oss tst = bst_oss st /\
  TORqsRel (tst_orqs tst) (bst_orqs st) /\
  TMsgsRel (tst_msgs tst) (bst_msgs st).

Definition tToMLabel (tlbl: TLabel) :=
  match tlbl with
  | RlblIns eins => RlblIns (imap tmsg_msg eins)
  | RlblOuts eouts => RlblOuts (imap tmsg_msg eouts)
  | RlblInt orule mins mouts =>
    RlblInt orule (imap tmsg_msg mins) (imap tmsg_msg mouts)
  end.

