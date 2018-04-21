Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.

Inductive step_m (sys: System): MState -> MLabel -> MState -> Prop :=
| SmSlt: forall st, step_m sys st emptyRLabel st
| SmExt: forall pst nst oss orqs oims emsg,
    fromExternal sys emsg = true ->
    toInternal sys emsg = true ->
    pst = {| bst_oss := oss; bst_orqs := orqs; bst_msgs := oims |} ->
    nst = {| bst_oss := oss;
             bst_orqs := orqs;
             bst_msgs := enqMP emsg oims
          |} ->
    step_m sys pst (RlblIn emsg) nst
| SmInt: forall pst nst oss orqs oims oidx os porq pos norq msgs rule outs,
    oidx = rule_oidx rule ->
    In oidx (indicesOf sys) ->
    oss@[oidx] = Some os ->
    orqs@[oidx] = Some porq ->
    Forall (FirstMP oims) msgs ->
    ValidMsgsIn oidx msgs ->
    map (fun tmsg => msg_id tmsg) msgs = rule_mids rule ->
    In rule (sys_rules sys) ->
    rule_precond rule os porq msgs ->
    rule_postcond rule os porq msgs pos norq outs ->
    ValidMsgOuts oidx outs ->

    pst = {| bst_oss := oss; bst_orqs := orqs; bst_msgs := oims |} ->
    nst = {| bst_oss := oss +[ oidx <- pos ];
             bst_orqs := orqs +[ oidx <- norq ];
             bst_msgs := distributeMsgs
                           (intOuts sys outs)
                           (removeMsgs msgs oims)
          |} ->

    step_m sys pst (RlblOuts (Some rule) msgs outs) nst.

