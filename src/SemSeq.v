Require Import Bool List String Peano_dec.
Require Import Permutation.
Require Import Common FMap Syntax Semantics.

Record AtomicMsg :=
  { atm_msg : Msg;
    atm_active : bool
  }.

Instance AtomicMsg_HasMsg : HasMsg AtomicMsg :=
  { getMsg := atm_msg }.

Section ToAtomicMsg.

  Definition toAtomicMsgs (active: bool) (msgs: list Msg) :=
    map (fun m => {| atm_msg := m; atm_active := active |}) msgs.

  Definition toAtomicMsgsT := toAtomicMsgs true.
  Definition toAtomicMsgsF := toAtomicMsgs false.

  Definition toAtomicQ (active: bool) (q: Queue Msg) := toAtomicMsgs active q.
  Definition toAtomicC (active: bool) (cs: Channels Msg) :=
    M.map (toAtomicQ active) cs.
  Definition toAtomicMF (active: bool) (mf: MsgsFrom Msg) :=
    M.map (toAtomicC active) mf.
  Definition toAtomicM (active: bool) (msgs: Messages Msg) :=
    M.map (toAtomicMF active) msgs.

  Definition toAtomicState (active: bool) (st: State Msg) :=
    {| st_oss := st_oss st; st_msgs := toAtomicM active (st_msgs st) |}.

  Definition toAtomicStateT := toAtomicState true.
  Definition toAtomicStateF := toAtomicState false.

End ToAtomicMsg.

Section ToMsg.

  Definition atm2Msg (am: AtomicMsg) := getMsg am.
  Definition atm2Q (q: Queue AtomicMsg) := map atm2Msg q.
  Definition atm2C (cs: Channels AtomicMsg) := M.map atm2Q cs.
  Definition atm2MF (mf: MsgsFrom AtomicMsg) := M.map atm2C mf.
  Definition atm2M (msgs: Messages AtomicMsg) := M.map atm2MF msgs.

  Definition atm2State (st: State AtomicMsg) :=
    {| st_oss := st_oss st; st_msgs := atm2M (st_msgs st) |}.

End ToMsg.

Section Deactivation.

  Definition deactivate (am: AtomicMsg) :=
    {| atm_msg := atm_msg am; atm_active := false |}.
  Definition deactivateQ (q: Queue AtomicMsg) := map deactivate q.
  Definition deactivateC (cs: Channels AtomicMsg) := M.map deactivateQ cs.
  Definition deactivateMF (mf: MsgsFrom AtomicMsg) := M.map deactivateC mf.
  Definition deactivateM (msgs: Messages AtomicMsg) := M.map deactivateMF msgs.

End Deactivation.

Inductive step_seq (sys: System) : State AtomicMsg -> Label -> State AtomicMsg -> Prop :=
| SsSlt: forall s, step_seq sys s LblEmpty s
| SsInt: forall oss oims obj idx mf os pos fmsg fpmsg fidx fchn outs,
    In obj (sys_objs sys) ->
    idx = obj_idx obj ->
    oss@[idx] = Some os ->
    oims@[idx] = Some mf ->

    (atm_active fmsg = true \/ isExternal sys fidx = true) ->
    
    firstMF fidx fchn mf = Some fmsg ->
    msg_id (getMsg fmsg) = pmsg_mid fpmsg ->
    ValidMsgId fidx idx fchn (getMsg fmsg) ->
    In fpmsg (obj_trs obj) ->
    pmsg_precond fpmsg os ->
    pmsg_postcond fpmsg os (msg_value (getMsg fmsg)) pos ->
    outs = pmsg_outs fpmsg os (msg_value (getMsg fmsg)) ->
    step_seq sys {| st_oss := oss; st_msgs := oims |}
             (LblHdl (getMsg fmsg) (extOuts sys outs))
             {| st_oss := oss +[ idx <- pos ];
                st_msgs := distributeMsgs (toAtomicMsgsT (intOuts sys outs))
                                          (if isExternal sys fidx
                                           then deactivateM oims
                                           else oims) |}
| SsExt: forall from emsgs oss oims,
    isExternal sys from = true ->
    emsgs <> nil ->
    SubList (map (fun m => mid_to (msg_id m)) emsgs) (indicesOf sys) ->
    step_seq sys {| st_oss := oss; st_msgs := oims |}
             (LblIns emsgs)
             {| st_oss := oss; st_msgs := distributeMsgs (toAtomicMsgsF emsgs) oims |}.

