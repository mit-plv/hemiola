Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics StepDet.

Inductive step_seq (sys: System) : TState -> TLabel -> TState -> Prop :=
| SsSlt: forall st, step_seq sys st emptyILabel st
| SsExt: forall ts oss oims emsg,
    isExternal sys (mid_from (msg_id emsg)) = true ->
    isInternal sys (mid_to (msg_id emsg)) = true ->
    step_seq sys
             {| tst_oss := oss; tst_msgs := oims; tst_tid := ts |}
             (IlblIn (toTMsgU emsg))
             {| tst_oss := oss;
                tst_msgs := distributeMsg (toTMsgU emsg) oims;
                tst_tid := ts
             |}
| SsIntFwd: forall ts oss oims obj oidx os pos
                   (fmsg: TMsg) fpmsg fidx fchn outs,
    In obj (sys_objs sys) ->
    oidx = obj_idx obj ->
    (oss)@[oidx] = Some os ->

    isInternal sys (mid_from (msg_id (getMsg fmsg))) = true ->

    (* This is the only difference from [step_det]: internal forwarding happens
     * only for the current transaction.
     *)
    tmsg_tid fmsg = Some ts ->

    ValidMsgId fidx oidx fchn fmsg ->
    firstM fidx oidx fchn oims = Some fmsg ->

    msg_id (getMsg fmsg) = pmsg_mid fpmsg ->
    In fpmsg (obj_trs obj) ->
    pmsg_precond fpmsg os ->
    pmsg_postcond fpmsg os (msg_value (getMsg fmsg)) pos ->
    outs = pmsg_outs fpmsg os (msg_value (getMsg fmsg)) ->
    ValidOuts oidx outs ->

    step_seq sys
             {| tst_oss := oss; tst_msgs := oims; tst_tid := ts |}
             (IlblOuts (Some fmsg) (extOuts sys (toTMsgs ts outs)))
             {| tst_oss := oss +[ oidx <- pos ];
                tst_msgs := distributeMsgs (intOuts sys (toTMsgs ts outs)) oims;
                tst_tid := ts
             |}
| SsIntInit: forall ts nts (Hts: nts > ts) oss oims obj oidx os pos
                   (fmsg: TMsg) fpmsg fidx fchn outs,
    In obj (sys_objs sys) ->
    oidx = obj_idx obj ->
    (oss)@[oidx] = Some os ->

    tmsg_tid fmsg = None ->

    ValidMsgId fidx oidx fchn fmsg ->
    firstM fidx oidx fchn oims = Some fmsg -> 

    msg_id (getMsg fmsg) = pmsg_mid fpmsg ->
    In fpmsg (obj_trs obj) ->
    pmsg_precond fpmsg os ->
    pmsg_postcond fpmsg os (msg_value (getMsg fmsg)) pos ->
    outs = pmsg_outs fpmsg os (msg_value (getMsg fmsg)) ->
    ValidOuts oidx outs ->

    step_seq sys
             {| tst_oss := oss; tst_msgs := oims; tst_tid := ts |}
             (IlblOuts (Some (toTMsg nts (getMsg fmsg))) (extOuts sys (toTMsgs nts outs)))
             {| tst_oss := oss +[ oidx <- pos ];
                tst_msgs := distributeMsgs (intOuts sys (toTMsgs nts outs)) oims;
                tst_tid := nts
             |}.

