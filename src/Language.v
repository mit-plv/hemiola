Require Import Bool List String Peano_dec.
Require Import FunctionalExtensionality Permutation.
Require Import Common FMap.

Set Implicit Arguments.

Open Scope list.
Open Scope fmap.

Section Language.

  Definition IdxT := nat.

  (* A message is always either a request or a response. *)
  Inductive RqRs := Rq | Rs.
  Definition rrToNat (rr: RqRs) :=
    match rr with
    | Rq => 0
    | Rs => 1
    end.

  Variable MsgT: Type.
  Hypothesis (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2}).
  Variable ValT: Type.
  Hypothesis (valT_dec: forall m1 m2: ValT, {m1 = m2} + {m1 <> m2}).
  
  Variable StateT: Type.

  Record MsgId := { msg_rq : IdxT; (* an object that requests this message *)
                    msg_rs : IdxT; (* an object that responses this message *)
                    msg_type : MsgT;
                    msg_rqrs : RqRs;
                    msg_chn : IdxT (* which channel (queue) to use *)
                  }.

  Definition buildMsgId rq rs ty rr cn :=
    {| msg_rq := rq; msg_rs := rs; msg_type := ty; msg_rqrs := rr; msg_chn := cn |}.

  Definition msgId_dec: forall m1 m2: MsgId, {m1 = m2} + {m1 <> m2}.
  Proof. repeat decide equality. Defined.

  Definition isTrsPair (rq rs: MsgId) :=
    (if msg_rq rq ==n msg_rq rs then true else false)
      && (if msg_rs rq ==n msg_rs rs then true else false)
      && (if msgT_dec (msg_type rq) (msg_type rs) then true else false)
      && (match msg_rqrs rq, msg_rqrs rs with
          | Rq, Rs => true
          | _, _ => false
          end).

  Record Msg :=
    { msg_id: MsgId;
      msg_value: ValT
    }.

  Definition msg_dec: forall m1 m2: Msg, {m1 = m2} + {m1 <> m2}.
  Proof. repeat decide equality. Defined.

  Definition msgFrom (msg: MsgId) :=
    match msg_rqrs msg with
    | Rq => msg_rq msg
    | Rs => msg_rs msg
    end.

  Definition msgTo (msg: MsgId) :=
    match msg_rqrs msg with
    | Rq => msg_rs msg
    | Rs => msg_rq msg
    end.

  (* A set of output messages are valid if
   * 1) they are from the same source [idx],
   * 2) each target is not the source, and
   * 2) all targets are different to each others.
   * TODO? syntax may have to ensure [ValidOuts], or by well-formedness.
   *)
  Definition ValidOuts (idx: IdxT) (msgs: list Msg) :=
    Forall (fun m => msgFrom (msg_id m) = idx /\ msgTo (msg_id m) <> idx) msgs /\
    NoDup (map (fun m => msgTo (msg_id m)) msgs).

  Record PMsg :=
    { pmsg_mid: MsgId;
      pmsg_precond: StateT -> Prop;
      pmsg_outs: StateT -> ValT -> list Msg;
      pmsg_postcond: StateT (* prestate *) -> ValT -> StateT (* poststate *) -> Prop
    }.

  Definition CondT := StateT -> Prop.
  Definition CondImp (c1 c2: CondT) := forall st, c1 st -> c2 st.
  Definition postOf (pmsg: PMsg): CondT :=
    fun post => forall pre mt, pmsg_postcond pmsg pre mt post.
  Definition Disjoint (c1 c2: CondT) := forall st, c1 st -> c2 st -> False.

  Record Object :=
    { obj_idx: nat;
      obj_state_init: StateT;
      obj_pmsgs: list PMsg
    }.

  Definition System := list Object.
  Definition indicesOf (sys: System) := map (fun o => obj_idx o) sys.

  (*! Now about semantics *)

  Section Messages.
    Variable MEltT: Type.
    
    Definition Queue := list MEltT.
    Definition Channels := M.t (* channel index *) Queue.
    Definition MsgsFrom := M.t (* from *) Channels.
    Definition Messages := M.t (* to *) MsgsFrom.

    Definition firstQ (q: Queue) := hd_error q.
    Definition deq (q: Queue): Queue := tl q.
    Definition enq (m: MEltT) (q: Queue): Queue := q ++ (m :: nil).

    Definition findC (chn: IdxT) (cs: Channels): Queue :=
      ol2l cs@[chn].
    Definition firstC (chn: IdxT) (cs: Channels) :=
      cs@[chn] >>= (fun q => firstQ q).
    Definition deqC (chn: IdxT) (cs: Channels): Channels :=
      match cs@[chn] with
      | Some q => cs +[chn <- deq q]
      | None => cs
      end.
    Definition enqC (chn: IdxT) (m: MEltT) (cs: Channels): Channels :=
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
    Definition enqMF (from chn: IdxT) (m: MEltT) (mf: MsgsFrom): MsgsFrom :=
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
    Definition enqM (from to chn: IdxT) (m: MEltT) (msgs: Messages): Messages :=
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
    | SoSlt: forall os mf, step_obj obj os mf (buildLabel nil None nil) os mf
    | SoInt: forall os mf fidx fchn fmsg fpmsg pos,
        firstMF fidx fchn mf = Some fmsg ->
        msg_id fmsg = pmsg_mid fpmsg ->
        msgTo (msg_id fmsg) = obj_idx obj ->
        In fpmsg (obj_pmsgs obj) ->
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
                           (msg_chn (msg_id emsg))
                           emsg mf).

    Definition distributeMsg (msg: Msg) (msgs: Messages Msg): Messages Msg :=
      enqM (msgFrom (msg_id msg)) (msgTo (msg_id msg)) (msg_chn (msg_id msg)) msg msgs.
    
    Fixpoint distributeMsgs (nmsgs: list Msg) (msgs: Messages Msg): Messages Msg :=
      match nmsgs with
      | nil => msgs
      | msg :: nmsgs' =>
        distributeMsgs nmsgs' (distributeMsg msg msgs)
      end.

    Record State := { st_oss: ObjectStates; st_msgs: Messages Msg }.

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
        In obj sys ->
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

    Definition Trace := list Label.

    (* Note that the head is the youngest *)
    Inductive steps (sys: System) : State -> Trace -> State -> Prop :=
    | StepsNil: forall st, steps sys st nil st
    | StepsCons:
        forall st1 msgs st2,
          steps sys st1 msgs st2 ->
          forall lbl st3,
            step sys st2 lbl st3 ->
            steps sys st1 (lbl :: msgs) st3.

    Fixpoint getObjectStatesInit (obs: list Object) : ObjectStates :=
      match obs with
      | nil => M.empty _
      | obj :: sys' =>
        M.add (obj_idx obj)
              (obj_state_init obj)
              (getObjectStatesInit sys')
      end.

    Definition getStateInit (sys: System) :=
      {| st_oss := getObjectStatesInit sys;
         st_msgs := M.empty _ |}.

    Definition activeLabel (l: Label) :=
      match l with
      | {| lbl_ins := nil; lbl_hdl := _; lbl_outs := nil |} => None
      | _ => Some l
      end.

    Fixpoint behaviorOf (tr: Trace): Trace :=
      match tr with
      | nil => nil
      | l :: tr' => (activeLabel l) ::> (behaviorOf tr')
      end.

    Inductive Behavior: System -> Trace -> Prop :=
    | Behv: forall sys tr st,
        steps sys (getStateInit sys) tr st ->
        forall btr,
          btr = behaviorOf tr ->
          Behavior sys btr.

    (** Now about linearizability *)

    (* In message passing system, a "process" (or "thread") refers to a 
     * "requester" and an "objects" (or "system") refers to a "requestee".
     * Thus, for a given message {| msg_rq := i; msg_rs := j; msg_rqrs := _ |},
     * its requester (process) is "i" and the (target) object is "j".
     *)

    (* [sys] acts as a processor for [msg]. *)
    Definition asProcessor (sys: System) (msg: Msg) :=
      if msg_rq (msg_id msg) ?<n (indicesOf sys) then true else false.
    Definition asSystem (sys: System) (msg: Msg) :=
      if msg_rs (msg_id msg) ?<n (indicesOf sys) then true else false.

    Definition sysSubHistory (sys: System) (hst: list Msg) :=
      filter (asSystem sys) hst.
    Definition procSubHistory (sys: System) (hst: list Msg) :=
      filter (asProcessor sys) hst.

    (* For a given system [sys] and its trace [tr], the history of [tr] is an
     * object subhistory with respect to [sys], where [lbl_hdl] is ignored.
     *)
    Fixpoint historyOf (sys: System) (tr: Trace) :=
      match tr with
      | nil => nil
      | {| lbl_ins := ins; lbl_hdl := _; lbl_outs := outs |} :: tr' =>
        (sysSubHistory sys (outs ++ ins)) ++ (historyOf sys tr')
      end.

    Inductive History : System -> list Msg -> Prop :=
    | Hist: forall sys hst,
        Behavior sys hst ->
        History sys (historyOf sys hst).

    (* A history consisting only of requests and matching responses. *)
    Inductive Complete: list Msg -> Prop :=
    | CplNil: Complete nil
    | CplAdd:
        forall hst1 hst2 hst3,
          Complete (hst1 ++ hst2 ++ hst3) ->
          forall rq rs,
            isTrsPair (msg_id rq) (msg_id rs) = true ->
            forall chst,
              chst = hst1 ++ rq :: hst2 ++ rs :: hst3 ->
              Complete chst.

    Inductive SubHistory {A}: list A -> list A -> Prop :=
    | SlNil: SubHistory nil nil
    | SlAdd: forall l1 l2, SubHistory l1 l2 -> forall a, SubHistory (a :: l1) (a :: l2)
    | SlSkip: forall l1 l2, SubHistory l1 l2 -> forall a, SubHistory l1 (a :: l2).
    
    Definition ExtHistory {A} (l el: list A): Prop :=
      exists e, el = l ++ e.

    Fixpoint matchTrsPair (rq: Msg) (rss: list Msg) :=
      match rss with
      | nil => None
      | rs :: rss' =>
        if isTrsPair (msg_id rq) (msg_id rs) then Some rss'
        else match matchTrsPair rq rss' with
             | Some nrss => Some (rs :: nrss)
             | None => None
             end
      end.

    (* Assuming the history is well-formed. *)
    Fixpoint complete' (hst rss: list Msg): list Msg * list Msg :=
      match hst with
      | nil => (nil, rss)
      | msg :: hst' =>
        match msg_rqrs (msg_id msg) with
        | Rq => let (phst, prss) := complete' hst' rss in
                match matchTrsPair msg prss with
                | Some nrss => (msg :: phst, nrss)
                | None => (phst, prss)
                end
        | Rs => let (phst, prss) := complete' hst' rss in
                (msg :: phst, msg :: prss)
        end
      end.

    Definition complete (hst: list Msg) := fst (complete' hst nil).
    Definition WellFormed (hst: list Msg) := snd (complete' hst nil) = nil.

    Lemma complete_subList: forall hst, SubHistory (complete hst) hst.
    Proof.
    Admitted.
    
    Lemma complete_complete: forall hst, Complete (complete hst).
    Proof.
    Admitted.

    Lemma complete_maximal:
      forall hst chst,
        chst <> complete hst ->
        SubHistory chst hst -> Complete chst ->
        ~ SubHistory (complete hst) chst.
    Proof.
    Admitted.

    (* An informal definition of "sequential":
     * 1) The first message should be a request
     * 2) A matching response for each request should be right after the request.
     * 3) There might not be a matching response for the last request.
     *)
    Fixpoint Sequential' (hst: list Msg) (orq: option Msg) :=
      match hst with
      | nil => true
      | msg :: hst' =>
        match orq with
        | Some rq => isTrsPair (msg_id rq) (msg_id msg) && Sequential' hst' None
        | None => match msg_rqrs (msg_id msg) with
                  | Rq => Sequential' hst' (Some msg)
                  | Rs => false
                  end
        end
      end.
    Definition Sequential (hst: list Msg) := Sequential' hst None = true.
    Definition Concurrent (hst: list Msg) := ~ Sequential hst.

    Definition sequential_concurrent_dec:
      forall hst, {Sequential hst} + {Concurrent hst}.
    Proof.
      unfold Concurrent, Sequential; intros.
      destruct (Sequential' hst None).
      - left; reflexivity.
      - right; discriminate.
    Defined.

    (* A system is sequential when all possible histories are sequential. *)
    Definition SequentialSys (sys: System) :=
      forall hst, History sys hst -> Sequential (rev hst).

    Definition requestsOf (hst: list Msg) :=
      filter (fun m => match msg_rqrs (msg_id m) with
                       | Rq => true
                       | _ => false
                       end) hst.

    (* Two histories are equivalent if
     * 1) one history is a permutation of the other, and
     * 2) they have the same request orders per a process.
     *)
    Definition Equivalent (hst1 hst2: list Msg) :=
      Permutation hst1 hst2 /\
      forall obj, requestsOf (procSubHistory (obj :: nil) hst1) =
                  requestsOf (procSubHistory (obj :: nil) hst2).

    (* NOTE: this is actually not a fully correct definition:
     * Linearizability requires one more condition: any _strict_ transaction
     * orders are preserved by [lhst].
     * I'm currently not sure if we need the second condition for 
     * message-passing systems.
     *)
    Definition Linearizable (hst lhst: list Msg) :=
      Sequential lhst /\
      Equivalent (complete hst) lhst.

    (* A system is linear when all possible histories are linearizable. *)
    Definition Linear (sys: System) :=
      forall hst,
        History sys hst ->
        exists lhst, History sys lhst /\
                     Linearizable (rev hst) (rev lhst).

  End Semantics.

  Section Facts.

    Lemma subHistory_refl: forall {A} (l: list A), SubHistory l l.
    Proof.
      induction l; simpl; intros; constructor; auto.
    Qed.
    Hint Immediate subHistory_refl.

    Lemma extHistory_trans:
      forall {A} (l1 l2 l3: list A),
        ExtHistory l1 l2 -> ExtHistory l2 l3 -> ExtHistory l1 l3.
    Proof.
      unfold ExtHistory; intros.
      destruct H, H0; subst.
      eexists; rewrite <-app_assoc; reflexivity.
    Qed.

    Lemma equivalent_refl: forall hst, Equivalent hst hst.
    Proof.
      intros; unfold Equivalent; split; intros; reflexivity.
    Qed.
    Hint Immediate equivalent_refl.

  End Facts.

End Language.

Definition Refines {MsgT ValT} {IStateT SStateT}
           (msgT_dec: forall m1 m2: MsgT, {m1 = m2} + {m1 <> m2})
           (valT_dec: forall m1 m2: ValT, {m1 = m2} + {m1 <> m2})
           (impl: System MsgT ValT IStateT) (spec: System MsgT ValT SStateT) :=
  forall hst, Behavior msgT_dec valT_dec impl hst ->
              Behavior msgT_dec valT_dec spec hst.

Infix "-->" := CondImp (at level 30).
Infix "-*-" := Disjoint (at level 30).

Definition singleton {MsgT ValT StateT} (obj: Object MsgT ValT StateT)
  : System MsgT ValT StateT := obj :: nil.

Notation "[ obj ]" := (singleton obj).

