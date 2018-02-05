Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.

Inductive step_det (sys: System) : TState -> TLabel -> TState -> Prop :=
| SdSlt: forall st, step_det sys st emptyILabel st
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
                oss oims obj oidx os pos fmsg frule fidx fchn outs,
    In obj sys ->
    oidx = obj_idx obj ->
    (oss)@[oidx] = Some os ->

    firstMP fidx oidx fchn oims = Some fmsg -> 

    msg_id (getMsg fmsg) = rule_mid frule ->
    In frule (obj_rules obj) ->
    rule_precond frule os (msg_value (getMsg fmsg)) ->
    rule_postcond frule os (msg_value (getMsg fmsg)) pos outs ->
    ValidOuts oidx outs ->

    tinfo = match tmsg_info fmsg with
          | Some finfo => finfo
          | None => {| tinfo_tid := nts;
                       tinfo_rqin := tmsg_msg fmsg |}
          end ->

    step_det sys
             {| tst_oss := oss;
                tst_msgs := oims;
                tst_tid := ts
             |}
             (IlblOuts (Some fmsg) (toTMsgs tinfo outs))
             {| tst_oss := oss +[ oidx <- pos ];
                tst_msgs := distributeMsgs
                              (intOuts sys (toTMsgs tinfo outs))
                              (deqMP fidx oidx fchn oims);
                tst_tid := match tmsg_info fmsg with
                           | Some _ => ts
                           | None => nts
                           end
             |}.

Definition steps_det: Steps TState TLabel := steps step_det.

