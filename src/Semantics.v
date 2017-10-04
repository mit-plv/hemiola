Require Import Bool List String Peano_dec.
Require Import Common FMap Syntax.

Set Implicit Arguments.

Class HasMsg (MsgT: Type) :=
  { getMsg : MsgT -> Msg }.

Instance Msg_HasMsg : HasMsg Msg :=
  { getMsg := id }.

Section Messages.
  Variable (MsgT: Type).
  Context `{HasMsg MsgT}.

  Definition Queue := list MsgT.
  Definition Channels := M.t (* channel index *) Queue.
  Definition MsgsFrom := M.t (* from *) Channels.
  Definition Messages := M.t (* to *) MsgsFrom.

  Definition firstQ (q: Queue) := hd_error q.
  Definition deq (q: Queue): Queue := tl q.
  Definition enq (m: MsgT) (q: Queue): Queue := q ++ (m :: nil).
  Definition EmptyQ (q: Queue) := q = nil.

  Definition findC (chn: IdxT) (cs: Channels): Queue :=
    ol2l cs@[chn].
  Definition firstC (chn: IdxT) (cs: Channels) :=
    cs@[chn] >>= (fun q => firstQ q).
  Definition deqC (chn: IdxT) (cs: Channels): Channels :=
    match cs@[chn] with
    | Some q => cs +[chn <- deq q]
    | None => cs
    end.
  Definition enqC (chn: IdxT) (m: MsgT) (cs: Channels): Channels :=
    match cs@[chn] with
    | Some q => cs +[chn <- enq m q]
    | None => cs +[chn <- enq m nil]
    end.
  Definition EmptyC (cs: Channels) := forall chn, EmptyQ (findC chn cs).

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
  Definition enqMF (from chn: IdxT) (m: MsgT) (mf: MsgsFrom): MsgsFrom :=
    match mf@[from] with
    | Some cs => mf +[from <- enqC chn m cs]
    | None => mf +[from <- enqC chn m (M.empty _)]
    end.
  Definition EmptyMF (mf: MsgsFrom) :=
    forall from chn, EmptyQ (findMF from chn mf).

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
  Definition enqM (from to chn: IdxT) (m: MsgT) (msgs: Messages): Messages :=
    match msgs@[to] with
    | Some froms => msgs +[to <- enqMF from chn m froms]
    | None => msgs +[to <- enqMF from chn m (M.empty _)]
    end.
  Definition EmptyM (msgs: Messages) :=
    forall from to chn, EmptyQ (findM from to chn msgs).

  Lemma firstM_Some_inv:
    forall from to chn msgs m, firstM from to chn msgs = Some m ->
                               exists mf, msgs@[to] = Some mf /\ firstMF from chn mf = Some m.
  Proof.
    unfold firstM; intros.
    destruct msgs@[to]; simpl in *; [|discriminate].
    eexists; split; auto.
  Qed.

  Definition distributeMsg (msg: MsgT) (msgs: Messages): Messages :=
    enqM (mid_from (msg_id (getMsg msg)))
         (mid_to (msg_id (getMsg msg)))
         (mid_chn (msg_id (getMsg msg))) msg msgs.

  Fixpoint distributeMsgs (nmsgs: list MsgT) (msgs: Messages): Messages :=
    match nmsgs with
    | nil => msgs
    | msg :: nmsgs' =>
      distributeMsgs nmsgs' (distributeMsg msg msgs)
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

  Definition emptyLabel :=
    {| lbl_ins := nil; lbl_hdl := None; lbl_outs := nil |}.

  Definition ObjectStates := M.t StateT.

  Definition ValidMsgId (from to chn: IdxT) (msg: Msg) :=
    mid_from (msg_id msg) = from /\
    mid_to (msg_id msg) = to /\
    mid_chn (msg_id msg) = chn.

  (* A set of messages are "valid outputs" if
   * 1) they are from the same source [idx],
   * 2) each target is not the source, and
   * 3) all targets (pair of msgTo and channel) are different to each others.
   * TODO: syntax has to ensure [ValidOuts], or by well-formedness.
   *)
  Definition ValidOuts (idx: IdxT) (msgs: list Msg) :=
    Forall (fun m => mid_from (msg_id m) = idx /\ mid_to (msg_id m) <> idx) msgs /\
    NoDup (map (fun m => (mid_to (msg_id m), mid_chn (msg_id m))) msgs).

  (* [step_obj] is for a step by a single object that either handles an 
   * internal message, or receives an external message.
   * For an internal message:
   * 1) the message is nondeterministically picked, and
   * 2) a predicated message for [fmsg], which satisfies its precondition and
   *    postcondition, is nondeterministically picked to take a step.
   * For an external message: it just receives the message and add it to a 
   * proper queue.
   *)
  Inductive step_obj (obj: Object): StateT -> MsgsFrom Msg -> Label ->
                                    StateT -> MsgsFrom Msg -> Prop :=
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
      mid_to (msg_id emsg) = obj_idx obj ->
      mid_from (msg_id emsg) <> obj_idx obj ->
      step_obj obj os mf
               (buildLabel (o2l (Some emsg)) None nil)
               os (enqMF (mid_from (msg_id emsg))
                         (mid_chn (msg_id emsg))
                         emsg mf).

  Record State MsgT :=
    { st_oss: ObjectStates;
      st_msgs: Messages MsgT
    }.

  Definition DisjointState {MsgT} (st1 st2: State MsgT) :=
    M.Disj (st_oss st1) (st_oss st2) /\
    M.Disj (st_msgs st1) (st_msgs st2).

  Definition combineState {MsgT} (st1 st2: State MsgT) :=
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
  (*   | Some hmsg => lbl_ins l = nil /\ ValidOuts (mid_to (msg_id hmsg)) (lbl_outs l) *)
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
  Inductive step_sys (sys: System) : State Msg -> Label -> State Msg -> Prop :=
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
    | Some _ => Forall (fun m => isExternal sys (mid_to (msg_id m)) = true) (lbl_outs l)
    | _ => Forall (fun m => isExternal sys (mid_from (msg_id m)) = true) (lbl_ins l)
    end.

  Inductive step_mod : System -> State Msg -> Label -> State Msg -> Prop :=
  | StepMod:
      forall sys st1 l st2,
        step_sys sys st1 l st2 ->
        Hidden sys l ->
        step_mod sys st1 l st2.

  Definition intOuts (sys: System) (outs: list Msg) :=
    filter (fun m => isInternal sys (mid_to (msg_id m))) outs.
  Definition extOuts (sys: System) (outs: list Msg) :=
    filter (fun m => isExternal sys (mid_to (msg_id m))) outs.

  Definition Step MsgT := System -> State MsgT -> Label -> State MsgT -> Prop.
  
  (* NOTE: the head is the youngest *)
  Inductive steps {MsgT} (step: Step MsgT)
            (sys: System) : State MsgT -> list Label -> State MsgT -> Prop :=
  | StepsNil: forall st, steps step sys st nil st
  | StepsCons:
      forall st1 ll st2,
        steps step sys st1 ll st2 ->
        forall lbl st3,
          step sys st2 lbl st3 ->
          steps step sys st1 (lbl :: ll) st3.

  Definition steps_mod := steps step_mod.

  Fixpoint getObjectStatesInit (obs: list Object): ObjectStates :=
    match obs with
    | nil => M.empty _
    | obj :: sys' => (getObjectStatesInit sys') +[obj_idx obj <- obj_state_init obj]
    end.

  Definition getStateInit {MsgT} (sys: System): State MsgT :=
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

  Inductive Behavior {MsgT} (step: Step MsgT) : System -> Trace -> Prop :=
  | Behv: forall sys ll st,
      steps step sys (getStateInit sys) ll st ->
      forall tr,
        tr = behaviorOf ll ->
        Behavior step sys tr.

  Definition Refines {MsgI MsgS} (stepI: Step MsgI) (stepS: Step MsgS)
             (p: BLabel -> BLabel)
             (impl spec: System) :=
    forall ll, Behavior stepI impl ll ->
               Behavior stepS spec (map p ll).

End Semantics.

Lemma map_id:
  forall {A} (l: list A), map id l = l.
Proof.
  induction l; simpl; auto.
  rewrite IHl; auto.
Qed.

Notation "StI # StS |-- I <=[ P ] S" := (Refines StI StS P I S) (at level 30).
Notation "StI # StS |-- I ⊑[ P ] S" := (Refines StI StS P I S) (at level 30).

(* NOTE: use inversion lemmas instead of [unfold]. *)
Global Opaque toBLabel.

