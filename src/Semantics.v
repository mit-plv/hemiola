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

  Lemma firstC_Some_inv:
    forall chn cs m, firstC chn cs = Some m ->
                     exists q, cs@[chn] = Some q /\ firstQ q = Some m.
  Proof.
    unfold firstC; intros.
    destruct cs@[chn]; simpl in *; [|discriminate].
    eexists; split; auto.
  Qed.

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

  Lemma firstMF_Some_inv:
    forall from chn mf m, firstMF from chn mf = Some m ->
                          exists cs, mf@[from] = Some cs /\ firstC chn cs = Some m.
  Proof.
    unfold firstMF; intros.
    destruct mf@[from]; simpl in *; [|discriminate].
    eexists; split; auto.
  Qed.

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

  Lemma firstM_Some_inv:
    forall from to chn msgs m, firstM from to chn msgs = Some m ->
                               exists mf, msgs@[to] = Some mf /\ firstMF from chn mf = Some m.
  Proof.
    unfold firstM; intros.
    destruct msgs@[to]; simpl in *; [|discriminate].
    eexists; split; auto.
  Qed.

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

  Definition emptyLabel :=
    {| lbl_ins := nil; lbl_hdl := None; lbl_outs := nil |}.

  Definition ObjectStates := M.t StateT.

  Definition ValidMsgId (from to chn: IdxT) (msg: Msg) :=
    msgFrom (msg_id msg) = from /\
    msgTo (msg_id msg) = to /\
    mid_chn (msg_id msg) = chn.

  (* A set of messages are "valid outputs" if
   * 1) they are from the same source [idx],
   * 2) each target is not the source, and
   * 3) all targets (pair of msgTo and channel) are different to each others.
   * TODO: syntax has to ensure [ValidOuts], or by well-formedness.
   *)
  Definition ValidOuts (idx: IdxT) (msgs: list Msg) :=
    Forall (fun m => msgFrom (msg_id m) = idx /\ msgTo (msg_id m) <> idx) msgs /\
    NoDup (map (fun m => (msgTo (msg_id m), mid_chn (msg_id m))) msgs).

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
  | SoSlt: forall os mf, step_obj obj os mf emptyLabel os mf
  | SoInt: forall os mf fidx fchn fmsg fpmsg pos,
      firstMF fidx fchn mf = Some fmsg ->
      ValidMsgId fidx (obj_idx obj) fchn fmsg ->
      msg_id fmsg = pmsg_mid fpmsg ->
      In fpmsg (obj_trs obj) ->
      pmsg_precond fpmsg os ->
      pmsg_postcond fpmsg os (msg_value fmsg) pos ->
      (* ValidOuts (obj_idx obj) (pmsg_outs fpmsg os (msg_value fmsg)) -> *)
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
    | None, None => True (* exists from, ValidOuts from (lbl_ins lbl1 ++ lbl_ins lbl2) *)
    | _, _ => False
    end.

  Definition subtractMsgs (ms1 ms2: list Msg) :=
    filter (fun msg => if in_dec msg_dec msg ms2 then false else true) ms1.

  (* Definition ValidLabel (l: Label) := *)
  (*   match lbl_hdl l with *)
  (*   | Some hmsg => lbl_ins l = nil /\ ValidOuts (msgTo (msg_id hmsg)) (lbl_outs l) *)
  (*   | None => lbl_outs l = nil /\ exists from, ValidOuts from (lbl_ins l) *)
  (*   end. *)

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

  (* [step_sys] either lifts a step by [step_obj] to a given system, or
   * combines two steps.
   *)
  Inductive step_sys (sys: System) : State -> Label -> State -> Prop :=
  | SsLift: forall oss idx (obj: Object) (os: StateT)
                   oims mf lbl pos pmf,
      In obj (sys_objs sys) ->
      obj_idx obj = idx ->
      oss@[idx] = Some os ->
      oims@[idx] = Some mf -> 
      step_obj obj os mf lbl pos pmf ->
      step_sys sys {| st_oss := oss; st_msgs := oims |} lbl
               {| st_oss := oss +[idx <- pos];
                  st_msgs := oims +[idx <- pmf] |}
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

  Definition distributeMsg (msg: Msg) (msgs: Messages): Messages :=
    enqM (msgFrom (msg_id msg)) (msgTo (msg_id msg)) (mid_chn (msg_id msg)) msg msgs.
  
  Fixpoint distributeMsgs (nmsgs: list Msg) (msgs: Messages): Messages :=
    match nmsgs with
    | nil => msgs
    | msg :: nmsgs' =>
      distributeMsgs nmsgs' (distributeMsg msg msgs)
    end.
  
  Definition intOuts (sys: System) (outs: list Msg) :=
    filter (fun m => isInternal sys (msgTo (msg_id m))) outs.
  Definition extOuts (sys: System) (outs: list Msg) :=
    filter (fun m => isExternal sys (msgTo (msg_id m))) outs.

  Inductive step_det (sys: System) : State -> Label -> State -> Prop :=
  | SsdSlt: forall s, step_det sys s emptyLabel s
  | SsdInt: forall oss oims obj idx mf os pos fmsg fpmsg fidx fchn outs,
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
      (* ValidOuts idx outs -> *)

      step_det sys {| st_oss := oss; st_msgs := oims |}
               (buildLabel nil (Some fmsg) (extOuts sys outs))
               {| st_oss := oss +[ idx <- pos ];
                  st_msgs := distributeMsgs (intOuts sys outs) oims |}
  | SsdExt: forall from emsgs oss oims,
      ~ In from (indicesOf sys) ->
      emsgs <> nil ->
      (* ValidOuts from emsgs -> *)
      SubList (map (fun m => msgTo (msg_id m)) emsgs) (indicesOf sys) ->
      step_det sys {| st_oss := oss; st_msgs := oims |}
               (buildLabel emsgs None nil)
               {| st_oss := oss; st_msgs := distributeMsgs emsgs oims |}.

  Theorem step_step_det:
    forall sys s1 l s2, step sys s1 l s2 -> step_det sys s1 l s2.
  Proof.
  Admitted.

  Theorem step_det_step:
    forall sys s1 l s2, step_det sys s1 l s2 -> step sys s1 l s2.
  Proof.
  Admitted.

  (* Note that the head is the youngest *)
  Inductive steps (sys: System) : State -> list Label -> State -> Prop :=
  | StepsNil: forall st, steps sys st nil st
  | StepsCons:
      forall st1 ll st2,
        steps sys st1 ll st2 ->
        forall lbl st3,
          step sys st2 lbl st3 ->
          steps sys st1 (lbl :: ll) st3.

  Fixpoint getObjectStatesInit (obs: list Object): ObjectStates :=
    match obs with
    | nil => M.empty _
    | obj :: sys' => (getObjectStatesInit sys') +[obj_idx obj <- obj_state_init obj]
    end.

  Definition getStateInit (sys: System) :=
    {| st_oss := getObjectStatesInit (sys_objs sys);
       st_msgs := [] |}.

  Record BLabel :=
    { blbl_ins : list Msg;
      blbl_outs : list Msg
    }.

  Definition toBLabel (l: Label): option BLabel :=
    match l with
    | {| lbl_ins := nil; lbl_outs := nil |} => None
    | _ => Some {| blbl_ins := lbl_ins l;
                   blbl_outs := lbl_outs l |}
    end.

  Lemma toBLabel_None:
    forall hdl, toBLabel (buildLabel nil hdl nil) = None.
  Proof. auto. Qed.

  Lemma toBLabel_Some_1:
    forall ins hdl outs,
      ins <> nil ->
      toBLabel (buildLabel ins hdl outs) =
      Some {| blbl_ins := ins; blbl_outs := outs |}.
  Proof.
    simpl; intros.
    destruct ins; intuition idtac.
  Qed.

  Lemma toBLabel_Some_2:
    forall ins hdl outs,
      outs <> nil ->
      toBLabel (buildLabel ins hdl outs) =
      Some {| blbl_ins := ins; blbl_outs := outs |}.
  Proof.
    simpl; intros.
    destruct ins; intuition idtac.
    destruct outs; intuition idtac.
  Qed.

  Definition Trace := list BLabel.

  Fixpoint behaviorOf (ll: list Label): Trace :=
    match ll with
    | nil => nil
    | l :: tr' => (toBLabel l) ::> (behaviorOf tr')
    end.

  Inductive Behavior: System -> Trace -> Prop :=
  | Behv: forall sys tr st,
      steps sys (getStateInit sys) tr st ->
      forall btr,
        btr = behaviorOf tr ->
        Behavior sys btr.

  Definition Refines (p: BLabel -> BLabel) (impl spec: System) :=
    forall hst, Behavior impl hst ->
                Behavior spec (map p hst).

End Semantics.

Notation "I <=[ P ] S" := (Refines P I S) (at level 30).
Notation "I ⊑[ P ] S" := (Refines P I S) (at level 30).

Global Opaque toBLabel.

