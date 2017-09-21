Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics.

Inductive step_det (sys: System) : State -> Label -> State -> Prop :=
| SdSlt: forall s, step_det sys s emptyLabel s
| SdInt: forall oss oims obj idx mf os pos fmsg fpmsg fidx fchn outs,
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

    step_det sys {| st_oss := oss; st_msgs := oims |}
             (buildLabel nil (Some fmsg) (extOuts sys outs))
             {| st_oss := oss +[ idx <- pos ];
                st_msgs := distributeMsgs (intOuts sys outs) oims |}
| SdExt: forall from emsgs oss oims,
    ~ In from (indicesOf sys) ->
    emsgs <> nil ->
    SubList (map (fun m => msgTo (msg_id m)) emsgs) (indicesOf sys) ->
    step_det sys {| st_oss := oss; st_msgs := oims |}
             (buildLabel emsgs None nil)
             {| st_oss := oss; st_msgs := distributeMsgs emsgs oims |}.

Definition steps_det := steps step_det.

(*! Consistency between the modular and det. semantics *)

Theorem step_mod_step_det:
  forall sys s1 l s2, step_mod sys s1 l s2 -> step_det sys s1 l s2.
Proof.
Admitted.

Theorem step_det_step_mod:
  forall sys s1 l s2, step_det sys s1 l s2 -> step_mod sys s1 l s2.
Proof.
Admitted.

