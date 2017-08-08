Require Import Bool List String Peano_dec.
Require Import FunctionalExtensionality.
Require Import Tactics FMap.

Set Implicit Arguments.

Open Scope list.

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
                    msg_rqrs : RqRs
                  }.
  Definition msgId_dec: forall m1 m2: MsgId, {m1 = m2} + {m1 <> m2}.
  Proof. repeat decide equality. Defined.

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

  Definition buildMsgId rq rs ty rr :=
    {| msg_rq := rq; msg_rs := rs; msg_type := ty; msg_rqrs := rr |}.

  Record PMsg :=
    { pmsg_mid: MsgId;
      pmsg_precond: StateT -> Prop;
      pmsg_outs: StateT -> ValT -> list Msg;
      pmsg_postcond: StateT (* prestate *) -> ValT -> StateT (* poststate *) -> Prop
    }.

  Record Object :=
    { obj_idx: nat;
      obj_state_init: StateT;
      obj_pmsgs: list PMsg
    }.

  Definition System := list Object.

  Section Semantics.

    Definition isTrsPair (rq rs: MsgId) :=
      (if eq_nat_dec (msg_rq rq) (msg_rq rs) then true else false)
        && (if eq_nat_dec (msg_rs rq) (msg_rs rs) then true else false)
        && (if msgT_dec (msg_type rq) (msg_type rs) then true else false)
        && (match msg_rqrs rq, msg_rqrs rs with
            | Rq, Rs => true
            | _, _ => false
            end).

    Definition ObjectStates := M.t StateT.

    Definition MsgsFrom := M.t (* from *) (M.t (* rq(0) or rs(1) *) (list Msg)).

    Definition findMsgF (idx: IdxT) (rr: RqRs) (mf: MsgsFrom) :=
      match M.find idx mf with
      | Some m => match M.find (rrToNat rr) m with
                  | Some msgs => Some msgs
                  | None => None
                  end
      | None => None
      end.

    Definition addMsgF (idx: IdxT) (rr: RqRs) (msgs: list Msg) (mf: MsgsFrom) :=
      match M.find idx mf with
      | Some m => M.add idx (M.add (rrToNat rr) msgs m) mf
      | None => M.add idx (M.add (rrToNat rr) msgs (M.empty _)) mf
      end.

    Definition addMsg (idx: IdxT) (rr: RqRs) (msg: Msg) (mf: MsgsFrom) :=
      match M.find idx mf with
      | Some idxm => match M.find (rrToNat rr) idxm with
                     | Some rrm => M.add idx (M.add (rrToNat rr) (msg :: rrm) idxm) mf
                     | None => M.add idx (M.add (rrToNat rr) (msg :: nil) idxm) mf
                     end
      | None => M.add idx (M.add (rrToNat rr) (msg :: nil) (M.empty _)) mf
      end.

    Definition Messages := M.t (* to *) MsgsFrom.

    (* A set of output messages are valid if
     * 1) they are from the same source [idx] and
     * 2) all targets are different to each others.
     * TODO? syntax may have to ensure [ValidOuts], or by well-formedness.
     *)
    Definition ValidOuts (idx: IdxT) (msgs: list Msg) :=
      Forall (fun m => msgFrom (msg_id m) = idx) msgs /\
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
    Inductive step_obj (obj: Object):
      StateT -> MsgsFrom ->
      option Msg (* external in? *) -> option Msg (* handling *) -> list Msg (* outs *) ->
      StateT -> MsgsFrom -> Prop :=
    | SoInt:
        forall os msgs_from fidx fmsgT fmsg fmsgs fpmsg pos,
          findMsgF fidx fmsgT msgs_from = Some (fmsg :: fmsgs) ->
          msg_id fmsg = pmsg_mid fpmsg ->
          msgTo (msg_id fmsg) = obj_idx obj ->
          In fpmsg (obj_pmsgs obj) ->
          pmsg_precond fpmsg os ->
          pmsg_postcond fpmsg os (msg_value fmsg) pos ->
          ValidOuts (obj_idx obj) (pmsg_outs fpmsg os (msg_value fmsg)) ->
          step_obj obj os msgs_from
                   None (Some fmsg) (pmsg_outs fpmsg os (msg_value fmsg))
                   pos (addMsgF fidx fmsgT fmsgs msgs_from)
    | SoExt:
        forall os msgs_from emsg,
          msgTo (msg_id emsg) = obj_idx obj ->
          step_obj obj os msgs_from
                   (Some emsg) None nil
                   os (addMsg (msgFrom (msg_id emsg))
                              (msg_rqrs (msg_id emsg))
                              emsg msgs_from).

    Definition distributeMsg (msg: Msg) (msgs: Messages): Messages :=
      let from := msgFrom (msg_id msg) in
      let to := msgTo (msg_id msg) in
      match M.find to msgs with
      | Some toMsgs =>
        let added := match findMsgF from (msg_rqrs (msg_id msg)) toMsgs with
                     (* should be added last, since the head is the oldest *)
                     | Some fromMsgs => fromMsgs ++ (msg :: nil)
                     | None => msg :: nil
                     end in
        M.add to (addMsgF from (msg_rqrs (msg_id msg)) added toMsgs) msgs
      | None =>
        M.add to (addMsgF from (msg_rqrs (msg_id msg)) (msg :: nil) (M.empty _)) msgs
      end.

    Fixpoint distributeMsgs (nmsgs: list Msg) (msgs: Messages): Messages :=
      match nmsgs with
      | nil => msgs
      | msg :: nmsgs' =>
        distributeMsgs nmsgs' (distributeMsg msg msgs)
      end.

    Definition getIndices (sys: System) := map (fun o => obj_idx o) sys.

    Definition isInternal (indices: list nat) (idx: IdxT) :=
      if in_dec eq_nat_dec idx indices then true else false.
    Definition isExternal (indices: list nat) (idx: IdxT) :=
      if in_dec eq_nat_dec idx indices then false else true.

    Definition fromExt (sys: System) (omsg: option Msg) :=
      match omsg with
      | Some msg => if isExternal (getIndices sys) (msgFrom (msg_id msg))
                    then Some msg else None
      | None => None
      end.
    Definition toInts (sys: System) (msgs: list Msg) :=
      filter (fun pm => isInternal (getIndices sys) (msgTo (msg_id pm))) msgs.
    Definition toExts (sys: System) (msgs: list Msg) :=
      filter (fun pm => isExternal (getIndices sys) (msgTo (msg_id pm))) msgs.

    (* Comparing with the Kami label:
     * - [lbl_ins] corresponds to [enq] defined methods of fifos.
     * - [lbl_hdl] corresponds to a rule handling a message, which implicitly
     *   calls [deq] to fetch the message.
     * - [lbl_outs] corresponds to [enq] called methods to fifos.
     *)
    Record Label := { lbl_ins: list Msg;
                      lbl_hdl: option Msg;
                      lbl_outs: list Msg }.

    Record State := { st_oss: ObjectStates;
                      st_msgs: Messages }.

    Definition combineState (st1 st2: State) :=
      {| st_oss := M.union (st_oss st1) (st_oss st2);
         st_msgs := M.union (st_msgs st1) (st_msgs st2) |}.
    Infix "+s" := combineState (at level 30).

    Definition DisjointLabel (lbl1 lbl2: Label) :=
      match lbl_hdl lbl1, lbl_hdl lbl2 with
      | Some _, None => SubList (lbl_ins lbl2) (lbl_outs lbl1)
      | None, Some _ => SubList (lbl_ins lbl1) (lbl_outs lbl2)
      | None, None => NoDup (map (fun m => msgTo (msg_id m)) (lbl_ins lbl1 ++ lbl_ins lbl2))
      | _, _ => False
      end.

    (* ms1 - ms2 *)
    Definition subtractMsgs (ms1 ms2: list Msg) :=
      filter (fun msg => if in_dec msg_dec msg ms2 then false else true) ms1.

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
                     oims msgs_from msg_in msg_hdl msgs_out pos pmsgs_from,
        In obj sys ->
        obj_idx obj = idx ->
        M.find idx oss = Some os ->
        M.find idx oims = Some msgs_from -> 
        step_obj obj os msgs_from msg_in msg_hdl msgs_out pos pmsgs_from ->
        step_sys sys {| st_oss := oss; st_msgs := oims |}
                 {| lbl_ins := o2l msg_in;
                    lbl_hdl := msg_hdl;
                    lbl_outs := msgs_out |}
                 {| st_oss := M.add idx pos oss;
                    st_msgs := M.add idx pmsgs_from oims |}
    | SsComb:
        forall st11 lbl1 st12 st21 lbl2 st22,
          step_sys sys st11 lbl1 st12 ->
          step_sys sys st21 lbl2 st22 ->
          step_sys sys (st11 +s st21) (lbl1 +l lbl2) (st12 +s st22).

    Definition ValidLabel (lbl: Label) :=
      match lbl_hdl lbl with
      | Some _ => lbl_ins lbl = nil
      | None => lbl_outs lbl = nil
      end.

    Inductive step : System -> State -> Label -> State -> Prop :=
    | Step:
        forall sys st1 lbl st2,
          step_sys sys st1 lbl st2 ->
          ValidLabel lbl ->
          step sys st1 lbl st2.

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

    Fixpoint getObjectStatesInit (sys: System) : ObjectStates :=
      match sys with
      | nil => M.empty _
      | obj :: sys' =>
        M.add (obj_idx obj)
              (obj_state_init obj)
              (getObjectStatesInit sys')
      end.

    Definition getLabel (lbl: Label) :=
      match lbl with
      | {| lbl_ins := nil; lbl_hdl := None; lbl_outs := nil |} => None
      | _ => Some lbl
      end.

    Fixpoint behaviorOf (l: Trace) :=
      match l with
      | nil => nil
      | lbl :: l' => (getLabel lbl) ::> (behaviorOf l')
      end.

    Inductive Behavior: System -> list Label -> Prop :=
    | Behv: forall sys hst st,
        steps sys {| st_oss := getObjectStatesInit sys;
                     st_msgs := M.empty _ |} hst st ->
        forall bhst,
          bhst = behaviorOf hst ->
          Behavior sys bhst.

    (** Now about linearizability *)

    Fixpoint historyOf (l: list Label) :=
      match l with
      | nil => nil
      | {| lbl_ins := _; lbl_hdl := hdl; lbl_outs := outs |} :: l' =>
        outs ++ hdl ::> (historyOf l')
      end.

    Inductive History : System -> list Msg -> Prop :=
    | Hist: forall sys hst,
        Behavior sys hst ->
        History sys (historyOf hst).

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
    
    (* In message passing system, a "process" refers to a "requester" and an 
     * "object" refers to a "requestee".
     * Thus, for a given message {| msg_rq := i; msg_rs := j; msg_rqrs := _ |},
     * its requester (process) is "i" and the (target) object is "j".
     *)
    Definition isProcessOf (obj: Object) (msg: Msg) :=
      if eq_nat_dec (obj_idx obj) (msg_rq (msg_id msg)) then true else false.

    Definition isObjectOf (obj: Object) (msg: Msg) :=
      if eq_nat_dec (obj_idx obj) (msg_rs (msg_id msg)) then true else false.

    Definition objSubHistory (obj: Object) (hst: list Msg) :=
      filter (isObjectOf obj) hst.

    Definition procSubHistory (obj: Object) (hst: list Msg) :=
      filter (isProcessOf obj) hst.

    (* Two histories are equivalent iff any process subhistories are equal. *)
    Definition Equivalent (hst1 hst2: list Msg) :=
      forall i, procSubHistory i hst1 = procSubHistory i hst2.

    (* TODO: this is actually not a fully correct definition:
     * Linearizability requires one more condition: any _strict_ transaction
     * orders are preserved by [lhst].
     *)
    Definition Linearizable (hst lhst: list Msg) :=
      exists ehst,
        ExtHistory hst ehst /\
        Sequential lhst /\
        Equivalent (complete ehst) lhst.

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
      intros; unfold Equivalent; reflexivity.
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

Hint Immediate subHistory_refl extHistory_trans equivalent_refl.

