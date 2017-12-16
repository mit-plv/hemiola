Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.

Inductive step_det (sys: System) : MState -> MLabel -> MState -> Prop :=
| SdSlt: forall st, step_det sys st emptyILabel st
| SdExt: forall oss oims emsg,
    isExternal sys (mid_from (msg_id emsg)) = true ->
    isInternal sys (mid_to (msg_id emsg)) = true ->
    step_det sys
             {| st_oss := oss; st_msgs := oims |}
             (IlblIn emsg)
             {| st_oss := oss; st_msgs := distributeMsg emsg oims |}
| SdInt: forall oss oims obj oidx os pos fmsg fpmsg fidx fchn outs,
    In obj (sys_objs sys) ->
    oidx = obj_idx obj ->
    (oss)@[oidx] = Some os ->

    isExternal sys (mid_from (msg_id fmsg)) = true ->

    ValidMsgId fidx oidx fchn fmsg ->
    firstM fidx oidx fchn oims = Some fmsg -> 

    msg_id fmsg = pmsg_mid fpmsg ->
    In fpmsg (obj_trs obj) ->
    pmsg_precond fpmsg os ->
    pmsg_postcond fpmsg os (msg_value fmsg) pos ->
    outs = pmsg_outs fpmsg os (msg_value fmsg) ->
    ValidOuts oidx outs ->

    step_det sys
             {| st_oss := oss; st_msgs := oims |}
             (IlblOuts (Some fmsg) outs)
             {| st_oss := oss +[ oidx <- pos ];
                st_msgs := distributeMsgs (intOuts sys outs) oims
             |}.

Definition steps_det: Steps MState MLabel := steps step_det.

