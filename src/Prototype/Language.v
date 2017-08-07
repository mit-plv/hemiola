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

    Definition Messages := M.t (* to *) MsgsFrom.

    (* A set of output messages are valid if
     * 1) they are from the same source [idx] and
     * 2) all targets are different to each others.
     * TODO? syntax may have to ensure [ValidOuts], or by well-formedness.
     *)
    Definition ValidOuts (idx: IdxT) (msgs: list Msg) :=
      Forall (fun m => msgFrom (msg_id m) = idx) msgs /\
      NoDup (map (fun m => msgTo (msg_id m)) msgs).

    (* [step_obj] is for a step by an object that handles an internal message:
     * 1) First, an internal message is nondeterministically picked, and
     * 2) A predicated message for [fmsg], which satisfies its precondition and
     *    postcondition, is nondeterministically picked to take a step.
     *)
    Inductive step_obj (obj: Object):
      StateT -> MsgsFrom ->
      Msg (* in *) -> list Msg (* outs *) ->
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
                   fmsg (pmsg_outs fpmsg os (msg_value fmsg))
                   pos (addMsgF fidx fmsgT fmsgs msgs_from).

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

    (* [lbl_in] is [None] if a step is taken externally. *)
    Record Label := { lbl_in: option Msg;
                      lbl_outs: list Msg }.

    Record State := { st_oss: ObjectStates;
                      st_msgs: Messages }.

    (* [step_sys] covers an internal and external step in terms of a given 
     * system.
     *)
    Inductive step_sys (sys: System) : State -> Label -> State -> Prop :=
    | SsInt: forall oss idx (obj: Object) (os: StateT)
                    oims msgs_from msg_in msgs_out pos pmsgs_from,
        In obj sys ->
        obj_idx obj = idx ->
        M.find idx oss = Some os ->
        M.find idx oims = Some msgs_from -> 
        step_obj obj os msgs_from msg_in msgs_out pos pmsgs_from ->
        isInternal (getIndices sys) (msgFrom (msg_id msg_in)) = true ->
        step_sys sys {| st_oss := oss; st_msgs := oims |}
                 {| lbl_in := Some msg_in;
                    lbl_outs := toExts sys msgs_out |}
                 {| st_oss := M.add idx pos oss;
                    st_msgs := distributeMsgs (toInts sys msgs_out)
                                              (M.add idx pmsgs_from oims) |}
    | SsExt: forall oss oims emsg_in emsgs_out,
        isExternal (getIndices sys) (msgTo (msg_id emsg_in)) = true ->
        Forall (fun emsg => isExternal
                              (getIndices sys)
                              (msgFrom (msg_id emsg)) = true) emsgs_out ->
        step_sys sys {| st_oss := oss; st_msgs := oims |}
                 {| lbl_in := None;
                    lbl_outs := emsgs_out |}
                 {| st_oss := oss;
                    st_msgs := distributeMsgs emsgs_out oims |}.

    Definition DisjointSystem (sys1 sys2: System) :=
      NoDup (map (fun obj => obj_idx obj) sys1 ++ map (fun obj => obj_idx obj) sys2).
    Definition combineSystem (sys1 sys2: System) := sys1 ++ sys2.

    Definition combineState (st1 st2: State) :=
      {| st_oss := M.union (st_oss st1) (st_oss st2);
         st_msgs := M.union (st_msgs st1) (st_msgs st2) |}.

    Definition DisjointLabel (lbl1 lbl2: Label) :=
      match lbl_in lbl1, lbl_in lbl2 with
      | Some _, None => SubList (lbl_outs lbl2) (lbl_outs lbl1)
      | None, Some _ => SubList (lbl_outs lbl1) (lbl_outs lbl2)
      | None, None => True
      | _, _ => False
      end.

    (* ms1 - ms2 *)
    Definition subtractMsgs (ms1 ms2: list Msg) :=
      filter (fun msg => if in_dec msg_dec msg ms2 then false else true) ms1.

    Definition combineLabel (lbl1 lbl2: Label) :=
      match lbl_in lbl1, lbl_in lbl2 with
      | Some _, None => {| lbl_in := lbl_in lbl1;
                           lbl_outs := subtractMsgs (lbl_outs lbl1) (lbl_outs lbl2) |}
      | None, Some _ => {| lbl_in := lbl_in lbl2;
                           lbl_outs := subtractMsgs (lbl_outs lbl2) (lbl_outs lbl1) |}
      | None, None => {| lbl_in := None;
                         lbl_outs := (lbl_outs lbl1) ++ (lbl_outs lbl2) |}
      | _, _ => {| lbl_in := None; lbl_outs := nil |}
      end.

    Inductive step : System -> State -> Label -> State -> Prop :=
    | StepLift:
        forall sys st1 lbl st2,
          step_sys sys st1 lbl st2 ->
          step sys st1 lbl st2
    | StepComb:
        forall sys1 st11 lbl1 st12,
          step sys1 st11 lbl1 st12 ->
          forall sys2 st21 lbl2 st22,
            step sys2 st21 lbl2 st22 ->
            step (combineSystem sys1 sys2)
                 (combineState st11 st21)
                 (combineLabel lbl1 lbl2)
                 (combineState st12 st22).

    Definition ocons {A} (oa: option A) (l: list A) :=
      match oa with
      | Some a => a :: l
      | None => l
      end.
    Infix "::>" := ocons (at level 0).

    (* Note that the head is the youngest *)
    Inductive steps (sys: System) : State -> list Label -> State -> Prop :=
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

    Definition getLabel (sys: System) (lbl: Label) :=
      match lbl with
      | {| lbl_in := min; lbl_outs := mouts |} =>
        let ein := fromExt sys min in
        match ein, mouts with
        | None, nil => None
        | _, _ => Some {| lbl_in := ein; lbl_outs := mouts |}
        end
      end.

    Fixpoint behaviorOf (sys: System) (l: list Label) :=
      match l with
      | nil => nil
      | lbl :: l' => (getLabel sys lbl) ::> (behaviorOf sys l')
      end.

    Inductive Behavior: System -> list Label -> Prop :=
    | Behv: forall sys hst st,
        steps sys {| st_oss := getObjectStatesInit sys;
                     st_msgs := M.empty _ |} hst st ->
        forall bhst,
          bhst = behaviorOf sys hst ->
          Behavior sys bhst.

    (** Now about linearizability *)

    Fixpoint historyOf (sys: System) (l: list Label) :=
      match l with
      | nil => nil
      | {| lbl_in := min; lbl_outs := mouts |} :: l' =>
        mouts ++ min ::> (historyOf sys l')
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

