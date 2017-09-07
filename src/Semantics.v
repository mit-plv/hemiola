Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax.

Section Messages.
  
  Definition Queue := list Msg.
  Definition Channels := M.t (* channel index *) Queue.
  Definition MsgsFrom := M.t (* from *) Channels.
  Definition Messages := M.t (* to *) MsgsFrom.

  Definition firstQ (q: Queue) := hd_error q.
  Definition deq (q: Queue): Queue := tl q.
  Definition enq (m: Msg) (q: Queue): Queue := q ++ (m :: nil).

  Definition findC (chn: IdxT) (cs: Channels): Queue :=
    ol2l cs@[chn].
  Definition firstC (chn: IdxT) (cs: Channels) :=
    cs@[chn] >>= (fun q => firstQ q).
  Definition deqC (chn: IdxT) (cs: Channels): Channels :=
    match cs@[chn] with
    | Some q => cs +[chn <- deq q]
    | None => cs
    end.
  Definition enqC (chn: IdxT) (m: Msg) (cs: Channels): Channels :=
    match cs@[chn] with
    | Some q => cs +[chn <- enq m q]
    | None => cs +[chn <- enq m nil]
    end.

  Definition findMF (from chn: IdxT) (mf: MsgsFrom): Queue :=
    ol2l (mf@[from] >>= (fun cs => cs@[chn])).
  Definition firstMF (from chn: IdxT) (mf: MsgsFrom) :=
    mf@[from] >>= (fun cs => firstC chn cs).
  Definition deqMF (from chn: IdxT) (mf: MsgsFrom): MsgsFrom :=
    match mf@[from] with
    | Some cs => mf +[from <- deqC chn cs]
    | None => mf
    end.
  Definition enqMF (from chn: IdxT) (m: Msg) (mf: MsgsFrom): MsgsFrom :=
    match mf@[from] with
    | Some cs => mf +[from <- enqC chn m cs]
    | None => mf +[from <- enqC chn m (M.empty _)]
    end.

  Definition findM (from to chn: IdxT) (msgs: Messages): Queue :=
    ol2l (msgs@[to] >>= (fun froms => froms@[from] >>= (fun cs => cs@[chn]))). 
  Definition firstM (from to chn: IdxT) (msgs: Messages) :=
    msgs@[to] >>= (fun froms => firstMF from chn froms).
  Definition deqM (from to chn: IdxT) (msgs: Messages): Messages :=
    match msgs@[to] with
    | Some froms => msgs +[to <- deqMF from chn froms]
    | None => msgs
    end.
  Definition enqM (from to chn: IdxT) (m: Msg) (msgs: Messages): Messages :=
    match msgs@[to] with
    | Some froms => msgs +[to <- enqMF from chn m froms]
    | None => msgs +[to <- enqMF from chn m (M.empty _)]
    end.

End Messages.

Section Semantics.

  (* Comparing with the Kami label:
   * - [lbl_ins] corresponds to [enq] defined methods of fifos.
   * - [lbl_hdl] corresponds to a rule handling a message, which implicitly
   *   calls [deq] to fetch the message.
   * - [lbl_outs] corresponds to [enq] called methods to fifos.
   *)
  Record Label :=
    { lbl_ins: list Msg;
      lbl_hdl: option Msg;
      lbl_outs: list Msg }.
  
  Definition buildLabel ins hdl outs :=
    {| lbl_ins := ins; lbl_hdl := hdl; lbl_outs := outs |}.

  Definition ObjectStates := M.t StateT.

  (* A set of messages are "valid outputs" if
   * 1) they are from the same source [idx],
   * 2) each target is not the source, and
   * 3) all targets are different to each others.
   * TODO? syntax may have to ensure [ValidOuts], or by well-formedness.
   *)
  Definition ValidOuts (idx: IdxT) (msgs: list Msg) :=
    Forall (fun m => msgFrom (msg_id m) = idx /\ msgTo (msg_id m) <> idx) msgs /\
    NoDup (map (fun m => msgTo (msg_id m)) msgs).

  (* [step_obj] is for a step by a single object that either handles an 
   * internal message, or receives an external message.
   * For an internal message:
   * 1) the message is nondeterministically picked, and
   * 2) a predicated message for [fmsg], which satisfies its precondition and
   *    postcondition, is nondeterministically picked to take a step.
   * For an external message: it just receives the message and add it to a 
   * proper queue.
   *)
  Inductive step_obj (obj: Object): StateT -> MsgsFrom -> Label ->
                                    StateT -> MsgsFrom -> Prop :=
  | SoSlt: forall os mf, step_obj obj os mf (buildLabel nil None nil) os mf
  | SoInt: forall os mf fidx fchn fmsg fpmsg pos,
      firstMF fidx fchn mf = Some fmsg ->
      msg_id fmsg = pmsg_mid fpmsg ->
      msgTo (msg_id fmsg) = obj_idx obj ->
      In fpmsg (obj_trs obj) ->
      pmsg_precond fpmsg os ->
      pmsg_postcond fpmsg os (msg_value fmsg) pos ->
      ValidOuts (obj_idx obj) (pmsg_outs fpmsg os (msg_value fmsg)) ->
      step_obj obj os mf
               (buildLabel nil (Some fmsg) (pmsg_outs fpmsg os (msg_value fmsg)))
               pos (deqMF fidx fchn mf)
  | SoExt: forall os mf emsg,
      msgTo (msg_id emsg) = obj_idx obj ->
      msgFrom (msg_id emsg) <> obj_idx obj ->
      step_obj obj os mf
               (buildLabel (o2l (Some emsg)) None nil)
               os (enqMF (msgFrom (msg_id emsg))
                         (mid_chn (msg_id emsg))
                         emsg mf).

  Definition distributeMsg (msg: Msg) (msgs: Messages): Messages :=
    enqM (msgFrom (msg_id msg)) (msgTo (msg_id msg)) (mid_chn (msg_id msg)) msg msgs.
  
  Fixpoint distributeMsgs (nmsgs: list Msg) (msgs: Messages): Messages :=
    match nmsgs with
    | nil => msgs
    | msg :: nmsgs' =>
      distributeMsgs nmsgs' (distributeMsg msg msgs)
    end.

  Record State := { st_oss: ObjectStates; st_msgs: Messages }.

  Definition DisjointState (st1 st2: State) :=
    M.Disj (st_oss st1) (st_oss st2) /\
    M.Disj (st_msgs st1) (st_msgs st2).

  Definition combineState (st1 st2: State) :=
    {| st_oss := M.union (st_oss st1) (st_oss st2);
       st_msgs := M.union (st_msgs st1) (st_msgs st2) |}.
  Infix "+s" := combineState (at level 30).

  Definition CombinableLabel (lbl1 lbl2: Label) :=
    match lbl_hdl lbl1, lbl_hdl lbl2 with
    | Some _, None => SubList (lbl_ins lbl2) (lbl_outs lbl1)
    | None, Some _ => SubList (lbl_ins lbl1) (lbl_outs lbl2)
    | None, None => exists from, ValidOuts from (lbl_ins lbl1 ++ lbl_ins lbl2)
    | _, _ => False
    end.

  Definition subtractMsgs (ms1 ms2: list Msg) :=
    filter (fun msg => if in_dec msg_dec msg ms2 then false else true) ms1.

  Definition ValidLabel (l: Label) :=
    match lbl_hdl l with
    | Some hmsg => lbl_ins l = nil /\ ValidOuts (msgTo (msg_id hmsg)) (lbl_outs l)
    | None => lbl_outs l = nil /\ exists from, ValidOuts from (lbl_ins l)
    end.

  Definition combineLabel (lbl1 lbl2: Label) :=
    match lbl_hdl lbl1, lbl_hdl lbl2 with
    | Some _, None => {| lbl_ins := nil;
                         lbl_hdl := lbl_hdl lbl1;
                         lbl_outs := subtractMsgs (lbl_outs lbl1) (lbl_ins lbl2) |}
    | None, Some _ => {| lbl_ins := nil;
                         lbl_hdl := lbl_hdl lbl2;
                         lbl_outs := subtractMsgs (lbl_outs lbl2) (lbl_ins lbl1) |}
    | None, None => {| lbl_ins := (lbl_ins lbl1) ++ (lbl_ins lbl2);
                       lbl_hdl := None;
                       lbl_outs := nil |}
    | _, _ => {| lbl_ins := nil; lbl_hdl := None; lbl_outs := nil |}
    end.
  Infix "+l" := combineLabel (at level 30).

  Definition emptyLabel :=
    {| lbl_ins := nil; lbl_hdl := None; lbl_outs := nil |}.

  (* [step_sys] either lifts a step by [step_obj] to a given system, or
   * combines two steps.
   *)
  Inductive step_sys (sys: System) : State -> Label -> State -> Prop :=
  | SsLift: forall oss idx (obj: Object) (os: StateT)
                   oims mf lbl pos pmf,
      In obj (sys_objs sys) ->
      obj_idx obj = idx ->
      M.find idx oss = Some os ->
      M.find idx oims = Some mf -> 
      step_obj obj os mf lbl pos pmf ->
      step_sys sys {| st_oss := oss; st_msgs := oims |} lbl
               {| st_oss := M.add idx pos oss;
                  st_msgs := M.add idx pmf oims |}
  | SsComb:
      forall st11 lbl1 st12 st21 lbl2 st22,
        step_sys sys st11 lbl1 st12 ->
        step_sys sys st21 lbl2 st22 ->
        DisjointState st11 st21 -> DisjointState st12 st22 ->
        CombinableLabel lbl1 lbl2 ->
        step_sys sys (st11 +s st21) (lbl1 +l lbl2) (st12 +s st22).

  Definition isExternal (sys: System) (idx: IdxT) :=
    if idx ?<n (indicesOf sys) then false else true.
  Definition isInternal (sys: System) (idx: IdxT) :=
    if idx ?<n (indicesOf sys) then true else false.

  Definition Hidden (sys: System) (l: Label) :=
    match lbl_hdl l with
    | Some _ => Forall (fun m => isExternal sys (msgTo (msg_id m)) = true) (lbl_outs l)
    | _ => Forall (fun m => isExternal sys (msgFrom (msg_id m)) = true) (lbl_ins l)
    end.

  Inductive step : System -> State -> Label -> State -> Prop :=
  | Step:
      forall sys st1 l st2,
        step_sys sys st1 l st2 ->
        Hidden sys l ->
        step sys st1 l st2.

  (* Note that the head is the youngest *)
  Inductive steps (sys: System) : State -> list Label -> State -> Prop :=
  | StepsNil: forall st, steps sys st nil st
  | StepsCons:
      forall st1 ll st2,
        steps sys st1 ll st2 ->
        forall lbl st3,
          step sys st2 lbl st3 ->
          steps sys st1 (lbl :: ll) st3.

  Fixpoint getObjectStatesInit {Trs} (obs: list (ObjectFrame Trs)) : ObjectStates :=
    match obs with
    | nil => M.empty _
    | obj :: sys' =>
      M.add (obj_idx obj)
            (obj_state_init obj)
            (getObjectStatesInit sys')
    end.

  Definition getStateInit {Trs} (sys: SystemFrame Trs) :=
    {| st_oss := getObjectStatesInit (sys_objs sys);
       st_msgs := M.empty _ |}.

  Record ELabel :=
    { elbl_ins : list Msg;
      elbl_outs : list Msg
    }.

  Definition toELabel (l: Label): option ELabel :=
    match l with
    | {| lbl_ins := nil; lbl_outs := nil |} => None
    | _ => Some {| elbl_ins := lbl_ins l; elbl_outs := lbl_outs l |}
    end.

  Definition Trace := list ELabel.

  Fixpoint behaviorOf (ll: list Label): Trace :=
    match ll with
    | nil => nil
    | l :: tr' => (toELabel l) ::> (behaviorOf tr')
    end.

  Inductive Behavior: System -> Trace -> Prop :=
  | Behv: forall sys tr st,
      steps sys (getStateInit sys) tr st ->
      forall btr,
        btr = behaviorOf tr ->
        Behavior sys btr.

  Definition Refines (impl spec: System) :=
    forall hst, Behavior impl hst ->
                Behavior spec hst.

End Semantics.

Infix "<=" := Refines.
Infix "⊑" := Refines (at level 0).

