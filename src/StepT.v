Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax Semantics.

Fixpoint getTMsgsTInfo (tmsgs: list TMsg) :=
  match tmsgs with
  | nil => None
  | tmsg :: tmsgs' =>
    match tmsg_info tmsg with
    | Some ti => Some ti
    | None => getTMsgsTInfo tmsgs'
    end
  end.

Inductive step_t (sys: System): TState -> TLabel -> TState -> Prop :=
| SdSlt: forall st, step_t sys st emptyRLabel st
| SdExt: forall ts pst nst oss orqs oims emsg,
    fromExternal sys emsg = true ->
    toInternal sys emsg = true ->
    pst = {| tst_oss := oss; tst_orqs := orqs; tst_msgs := oims; tst_tid := ts |} ->
    nst = {| tst_oss := oss;
             tst_orqs := orqs;
             tst_msgs := enqMP (toTMsgU emsg) oims;
             tst_tid := ts
          |} ->
    step_t sys pst (RlblIn (toTMsgU emsg)) nst
| SdInt: forall ts pst nst nts (Hts: nts > ts) tinfo
                oss orqs oims oidx os porq pos norq msgs rule outs,
    In oidx (indicesOf sys) ->
    oss@[oidx] = Some os ->
    orqs@[oidx] = Some porq ->
    Forall (FirstMP oims) msgs ->
    ValidMsgsIn oidx msgs ->
    map (fun tmsg => msg_id (tmsg_msg tmsg)) msgs = rule_mids rule ->
    In rule (sys_rules sys) ->
    rule_precond rule os (map tmsg_msg porq) (map tmsg_msg msgs) ->
    rule_postcond rule os (map tmsg_msg porq) (map tmsg_msg msgs)
                  pos (map tmsg_msg norq) outs ->
    ValidMsgOuts oidx outs ->

    tinfo = match getTMsgsTInfo msgs with
            | Some ti => ti
            | None => {| tinfo_tid := nts; tinfo_rqin := map tmsg_msg msgs |}
            end ->

    pst = {| tst_oss := oss; tst_orqs := orqs; tst_msgs := oims; tst_tid := ts |} ->
    nst = {| tst_oss := oss +[ oidx <- pos ];
             tst_orqs := orqs +[ oidx <- norq ];
             tst_msgs := distributeMsgs
                           (intOuts sys (toTMsgs tinfo outs))
                           (removeMsgs msgs oims);
             tst_tid := match getTMsgsTInfo msgs with
                        | Some _ => ts
                        | None => nts
                        end
          |} ->

    step_t sys pst (RlblOuts (Some rule) msgs (toTMsgs tinfo outs)) nst.

