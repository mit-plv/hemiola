Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics.

Definition NoInternalsQ (sys: System) (q: Queue) :=
  Forall (fun m => isInternal sys (msgFrom (msg_id m)) = false) q.

Definition NoInternalsC (sys: System) (c: Channels) :=
  forall cidx, c@[cidx] >>=[True] (fun q => NoInternalsQ sys q).

Definition NoInternalsMF (sys: System) (mf: MsgsFrom) :=
  forall fr, mf@[fr] >>=[True] (fun c => NoInternalsC sys c).

Definition NoInternalsM (sys: System) (msgs: Messages) :=
  forall to, msgs@[to] >>=[True] (fun mf => NoInternalsMF sys mf).

Inductive step_seq (sys: System) : State -> Label -> State -> Prop :=
| SsSlt: forall s, step_seq sys s emptyLabel s
| SsInt: forall oss oims obj idx mf os pos fmsg fpmsg fidx fchn outs,
    In obj (sys_objs sys) ->
    idx = obj_idx obj ->
    oss@[idx] = Some os ->
    oims@[idx] = Some mf ->

    firstMF fidx fchn mf = Some fmsg ->
    msg_id fmsg = pmsg_mid fpmsg ->
    ValidMsgId fidx idx fchn fmsg ->
    In fpmsg (obj_trs obj) ->
    pmsg_precond fpmsg os ->
    pmsg_postcond fpmsg os (msg_value fmsg) pos ->
    outs = pmsg_outs fpmsg os (msg_value fmsg) ->

    (* This is the only one additional condition compared with [step_mod];
     * The system starts handling external messages only when there are no internal
     * messages.
     *)
    (isExternal sys fidx = true -> NoInternalsM sys oims) ->

    step_seq sys {| st_oss := oss; st_msgs := oims |}
             (buildLabel nil (Some fmsg) (extOuts sys outs))
             {| st_oss := oss +[ idx <- pos ];
                st_msgs := distributeMsgs (intOuts sys outs) oims |}
| SsExt: forall from emsgs oss oims,
    ~ In from (indicesOf sys) ->
    emsgs <> nil ->
    SubList (map (fun m => msgTo (msg_id m)) emsgs) (indicesOf sys) ->
    step_seq sys {| st_oss := oss; st_msgs := oims |}
             (buildLabel emsgs None nil)
             {| st_oss := oss; st_msgs := distributeMsgs emsgs oims |}.

