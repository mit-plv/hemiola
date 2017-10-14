Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics StepDet Serial.

Record ATState : Type :=
  { atst_oss : ObjectStates;
    atst_msgs : Messages TMsg;
    atst_tid : TrsId;
    atst_cur : TrsId
  }.

Definition getATStateInit (sys: System): ATState :=
  {| atst_oss := getObjectStatesInit (sys_objs sys);
     atst_msgs := [];
     atst_tid := trsIdInit;
     atst_cur := trsIdInit
  |}.

Instance ATState_HasInit: HasInit ATState :=
  { getStateInit := getATStateInit }.

Definition at2TState (ats: ATState) :=
  {| tst_oss := atst_oss ats;
     tst_msgs := atst_msgs ats;
     tst_tid := atst_tid ats |}.

Inductive step_seq (sys: System) : ATState -> TLabel -> ATState -> Prop :=
| SsSlt: forall st, step_seq sys st emptyILabel st
| SsInt: forall ts cts oss oims obj idx os pos (fmsg: TMsg) fpmsg fidx fchn outs,
    In obj (sys_objs sys) ->
    idx = obj_idx obj ->
    oss@[idx] = Some os ->

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
             {| atst_oss := oss;
                atst_msgs := oims;
                atst_tid := ts;
                atst_cur := cts |}
             (IlblInt (Some fmsg) (extOuts sys (toTMsgs (tmsg_tid fmsg) outs)))
             {| atst_oss := oss +[ idx <- pos ];
                atst_msgs := distributeMsgs (intOuts sys (toTMsgs (tmsg_tid fmsg) outs)) oims;
                atst_tid := ts;
                atst_cur := cts |}

| SsExt: forall ts cts nts (Hts: nts > ts) oss oims obj os pos (emsg: Msg) fpmsg outs,
    In obj (sys_objs sys) ->
    oss@[obj_idx obj] = Some os ->

    isExternal sys (mid_from (msg_id emsg)) = true ->
    isInternal sys (mid_to (msg_id emsg)) = true ->

    msg_id emsg = pmsg_mid fpmsg ->
    In fpmsg (obj_trs obj) ->
    pmsg_precond fpmsg os ->
    pmsg_postcond fpmsg os (msg_value emsg) pos ->
    outs = pmsg_outs fpmsg os (msg_value emsg) ->
    ValidOuts (obj_idx obj) outs ->

    step_seq sys
             {| atst_oss := oss;
                atst_msgs := oims;
                atst_tid := ts;
                atst_cur := cts |}
             (IlblExt {| tmsg_msg := emsg; tmsg_tid := ts |} (extOuts sys (toTMsgs ts outs)))
             {| atst_oss := oss +[ obj_idx obj <- pos ];
                atst_msgs := distributeMsgs (intOuts sys (toTMsgs ts outs)) oims;
                atst_tid := nts;
                atst_cur := nts |}.

