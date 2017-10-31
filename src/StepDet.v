Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.

Inductive step_det (sys: System) : TState -> TLabel -> TState -> Prop :=
| SdSlt: forall st, step_det sys st emptyILabel st
| SdInt: forall ts oss oims obj oidx os pos (fmsg: TMsg) fpmsg fidx fchn outs,
    In obj (sys_objs sys) ->
    oidx = obj_idx obj ->
    (oss)@[oidx] = Some os ->

    isInternal sys (mid_from (msg_id (getMsg fmsg))) = true ->

    ValidMsgId fidx oidx fchn fmsg ->
    firstM fidx oidx fchn oims = Some fmsg -> 

    msg_id (getMsg fmsg) = pmsg_mid fpmsg ->
    In fpmsg (obj_trs obj) ->
    pmsg_precond fpmsg os ->
    pmsg_postcond fpmsg os (msg_value (getMsg fmsg)) pos ->
    outs = pmsg_outs fpmsg os (msg_value (getMsg fmsg)) ->
    ValidOuts oidx outs ->

    step_det sys
             {| tst_oss := oss; tst_msgs := oims; tst_tid := ts |}
             (IlblInt (Some fmsg) (extOuts sys (toTMsgs (tmsg_tid fmsg) outs)))
             {| tst_oss := oss +[ oidx <- pos ];
                tst_msgs := distributeMsgs (intOuts sys (toTMsgs (tmsg_tid fmsg) outs)) oims;
                tst_tid := ts
             |}

| SdExt: forall ts nts (Hts: nts > ts) oss oims obj oidx os pos (emsg: Msg) fpmsg outs,
    In obj (sys_objs sys) ->
    oidx = obj_idx obj ->
    oss@[oidx] = Some os ->

    isExternal sys (mid_from (msg_id emsg)) = true ->

    msg_id emsg = pmsg_mid fpmsg ->
    In fpmsg (obj_trs obj) ->
    pmsg_precond fpmsg os ->
    pmsg_postcond fpmsg os (msg_value emsg) pos ->
    outs = pmsg_outs fpmsg os (msg_value emsg) ->
    ValidOuts oidx outs ->

    step_det sys
             {| tst_oss := oss; tst_msgs := oims; tst_tid := ts |}
             (IlblExt {| tmsg_msg := emsg; tmsg_tid := nts |} (extOuts sys (toTMsgs nts outs)))
             {| tst_oss := oss +[ oidx <- pos ];
                tst_msgs := distributeMsgs (intOuts sys (toTMsgs ts outs)) oims;
                tst_tid := nts
             |}.

Definition steps_det := steps step_det.

