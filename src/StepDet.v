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
                tst_msgs := distributeMsg (toTMsgU emsg) oims;
                tst_tid := ts
             |}
| SdInt: forall ts nts (Hts: nts > ts) tts
                oss oims obj oidx os pos fmsg frule fidx fchn outs,
    In obj (sys_objs sys) ->
    oidx = obj_idx obj ->
    (oss)@[oidx] = Some os ->

    isExternal sys (mid_from (msg_id (getMsg fmsg))) = true ->

    ValidMsgId fidx oidx fchn (getMsg fmsg) ->
    firstM fidx oidx fchn oims = Some fmsg -> 

    msg_id (getMsg fmsg) = rule_mid frule ->
    In frule (obj_rules obj) ->
    rule_precond frule os ->
    rule_postcond frule os (msg_value (getMsg fmsg)) pos ->
    outs = rule_outs frule os (msg_value (getMsg fmsg)) ->
    ValidOuts oidx outs ->

    tts = match tmsg_tid fmsg with
          | Some tid => tid
          | None => nts
          end ->

    step_det sys
             {| tst_oss := oss;
                tst_msgs := oims;
                tst_tid := ts
             |}
             (IlblOuts (Some (toTMsg tts (getMsg fmsg))) (toTMsgs tts outs))
             {| tst_oss := oss +[ oidx <- pos ];
                tst_msgs := distributeMsgs (intOuts sys (toTMsgs tts outs)) oims;
                tst_tid := match tmsg_tid fmsg with
                           | Some _ => ts
                           | None => nts
                           end
             |}.

Definition steps_det: Steps TState TLabel := steps step_det.

