Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics StepDet Serial.

Inductive step_seq (sys: System) : TState -> TLabel -> TState -> Prop :=
| SsSlt: forall st, step_seq sys st emptyILabel st
| SsInt: forall ts oss oims obj idx os pos (fmsg: TMsg) fpmsg fidx fchn outs,
    In obj (sys_objs sys) ->
    idx = obj_idx obj ->
    oss@[idx] = Some os ->

    isInternal sys (mid_from (msg_id (getMsg fmsg))) = true ->

    firstM fidx idx fchn oims = Some fmsg -> 
    msg_id (getMsg fmsg) = pmsg_mid fpmsg ->
    ValidMsgId fidx idx fchn fmsg ->
    In fpmsg (obj_trs obj) ->
    pmsg_precond fpmsg os ->
    pmsg_postcond fpmsg os (msg_value (getMsg fmsg)) pos ->
    outs = pmsg_outs fpmsg os (msg_value (getMsg fmsg)) ->
    ValidOuts (obj_idx obj) outs ->

    (* For internal steps, below is the only additional condition from [step_det]. *)
    tmsg_tid fmsg = ts ->

    step_seq sys
             {| tst_oss := oss;
                tst_msgs := oims;
                tst_tid := ts |}
             (IlblInt (Some fmsg) (extOuts sys (toTMsgs (tmsg_tid fmsg) outs)))
             {| tst_oss := oss +[ idx <- pos ];
                tst_msgs := distributeMsgs (intOuts sys (toTMsgs (tmsg_tid fmsg) outs)) oims;
                tst_tid := ts |}

| SsExt: forall ts nts (Hts: nts > ts) oss oims obj os pos (emsg: Msg) fpmsg outs,
    In obj (sys_objs sys) ->
    oss@[obj_idx obj] = Some os ->

    isExternal sys (mid_from (msg_id emsg)) = true ->

    msg_id emsg = pmsg_mid fpmsg ->
    In fpmsg (obj_trs obj) ->
    pmsg_precond fpmsg os ->
    pmsg_postcond fpmsg os (msg_value emsg) pos ->
    outs = pmsg_outs fpmsg os (msg_value emsg) ->
    ValidOuts (obj_idx obj) outs ->

    step_seq sys
             {| tst_oss := oss;
                tst_msgs := oims;
                tst_tid := ts |}
             (IlblExt {| tmsg_msg := emsg; tmsg_tid := nts |} (extOuts sys (toTMsgs nts outs)))
             {| tst_oss := oss +[ obj_idx obj <- pos ];
                tst_msgs := distributeMsgs (intOuts sys (toTMsgs ts outs)) oims;
                tst_tid := nts |}.

