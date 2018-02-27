Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.

Fixpoint getTMsgsTInfo (tmsgs: list TMsg) :=
  match tmsgs with
  | nil => None
  | tmsg :: tmsgs' =>
    match tmsg_info tmsg with
    | Some ti => Some ti
    | None => getTMsgsTInfo tmsgs'
    end
  end.

Inductive step_det (sys: System OrdOState): TState -> TLabel -> TState -> Prop :=
| SdSlt: forall st, step_det sys st emptyRLabel st
| SdExt: forall ts oss oims emsg,
    isExternal sys (mid_from (msg_id emsg)) = true ->
    isInternal sys (mid_to (msg_id emsg)) = true ->
    step_det sys
             {| tst_oss := oss;
                tst_msgs := oims;
                tst_tid := ts
             |}
             (IlblIn (toTMsgU emsg))
             {| tst_oss := oss;
                tst_msgs := enqMP (toTMsgU emsg) oims;
                tst_tid := ts
             |}
| SdInt: forall ts nts (Hts: nts > ts) tinfo
                oss oims obj oidx os pos msgs rule outs,
    In obj sys ->
    oidx = obj_idx obj ->
    (oss)@[oidx] = Some os ->

    Forall (FirstMP oims) msgs ->
    ValidMsgsIn oidx msgs ->
    map (fun tmsg => msg_id (tmsg_msg tmsg)) msgs = rule_mids rule ->
    In rule (obj_rules obj) ->
    rule_precond rule os (map tmsg_msg msgs) ->
    rule_postcond rule os (map tmsg_msg msgs) pos outs ->
    ValidMsgOuts oidx outs ->

    tinfo = match getTMsgsTInfo msgs with
            | Some ti => ti
            | None => {| tinfo_tid := nts; tinfo_rqin := map tmsg_msg msgs |}
            end ->

    step_det sys
             {| tst_oss := oss;
                tst_msgs := oims;
                tst_tid := ts
             |}
             (IlblOuts (Some rule) msgs (toTMsgs tinfo outs))
             {| tst_oss := oss +[ oidx <- pos ];
                tst_msgs := distributeMsgs
                              (intOuts sys (toTMsgs tinfo outs))
                              (removeMsgs msgs oims);
                tst_tid := match getTMsgsTInfo msgs with
                           | Some _ => ts
                           | None => nts
                           end
             |}.

Definition steps_det: Steps (System OrdOState) TState TLabel := steps step_det.

