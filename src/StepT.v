Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics StepM.

Open Scope list.
Open Scope fmap.

(* NOTE: [getTMsgsTInfo] and [isExternalResp] are both used just for
 * annotating extra information about messages. We will be able to 
 * prove some properties about messages using this information,
 * assuming we only have a certain sort of [Rule]s (state transitions).
 * Even if below definitions seem to be incomplete, it is totally fine
 * because of the assumptions about [Rule]s.
 *)

Fixpoint getTMsgsTInfo (tmsgs: list TMsg) :=
  match tmsgs with
  | nil => None
  | tmsg :: tmsgs' =>
    match tmsg_info tmsg with
    | Some ti => Some ti
    | None => getTMsgsTInfo tmsgs'
    end
  end.

Fixpoint isExternalResp {MsgT} (merss: list IdxT) (outs: list (Id MsgT)) :=
  match outs with
  | nil => false
  | out :: outs' =>
    if (idOf out) ?<n merss
    then true
    else isExternalResp merss outs'
  end.

Inductive step_t (sys: System): TState -> TLabel -> TState -> Prop :=
| StSlt: forall st, step_t sys st (RlblEmpty _) st
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
    Forall (FirstMPI msgs) eouts ->
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

| StInt: forall oidx obj rule
                ts pst nst nts (Hts: nts > ts) tinfo
                oss orqs msgs trss os porq pos norq ins outs
                (Hifc: ost_ifc os = obj_ifc obj),
    In obj (sys_objs sys) ->
    In rule (obj_rules obj) ->
    oidx = obj_idx obj ->

    oss@[oidx] = Some os ->
    orqs@[oidx] = Some porq ->
    
    Forall (FirstMPI msgs) ins ->
    ValidMsgsIn sys ins ->
    idsOf ins = rule_minds rule ->
    map (fun tmsg => msg_id (getMsg tmsg)) (valsOf ins) = rule_msg_ids rule ->
    
    rule_precond rule (match Hifc with eq_refl => ost_st os end)
                 (orqMap tmsg_msg porq) (imap tmsg_msg ins) ->
    rule_trs rule (match Hifc with eq_refl => ost_st os end)
             (orqMap tmsg_msg porq) (imap tmsg_msg ins)
    = (pos, orqMap tmsg_msg norq, outs) ->
    ValidMsgsOut sys outs ->

    DisjList (idsOf ins) (idsOf outs) ->
    
    tinfo = match getTMsgsTInfo (valsOf ins) with
            | Some ti => ti
            | None => {| tinfo_tid := nts;
                         tinfo_rqin := imap tmsg_msg ins |}
            end ->

    pst = {| tst_oss := oss; tst_orqs := orqs;
             tst_msgs := msgs; tst_trss := trss; tst_tid := ts |} ->
    nst = {| tst_oss := oss +[ oidx <- {| ost_st := pos |} ];
             tst_orqs := orqs +[ oidx <- norq ];
             tst_msgs := enqMsgs (imap (toTMsg tinfo) outs)
                                 (deqMsgs (idsOf ins) msgs);
             tst_trss :=
               if isExternalResp (sys_merss sys) outs
               then enqMsgs (imap (toTMsg tinfo) outs)
                            (deqMsgs (idsOf (tinfo_rqin tinfo)) msgs)
               else msgs;
             tst_tid := match getTMsgsTInfo (valsOf ins) with
                        | Some _ => ts
                        | None => nts
                        end
          |} ->

    step_t sys pst (RlblInt oidx (rule_idx rule) ins (imap (toTMsg tinfo) outs)) nst.

Definition TORqsRel (torqs: ORqs TMsg) (orqs: ORqs Msg) :=
  forall oidx,
    match torqs@[oidx], orqs@[oidx] with
    | Some torq, Some orq => orqMap tmsg_msg torq = orq
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
  | RlblEmpty _ => RlblEmpty _
  | RlblIns eins => RlblIns (imap tmsg_msg eins)
  | RlblOuts eouts => RlblOuts (imap tmsg_msg eouts)
  | RlblInt oidx ridx mins mouts =>
    RlblInt oidx ridx (imap tmsg_msg mins) (imap tmsg_msg mouts)
  end.

Close Scope list.
Close Scope fmap.

