Require Import Bool List String Peano_dec.
Require Import FnMap.

Set Implicit Arguments.

Open Scope list.

Section Language.

  Definition IdxT := nat.

  (* A message is always either a request or a response. *)
  Inductive RqRs := Rq | Rs.

  (** Utilities *)
  Definition idx_add {A} (k: IdxT) (v: A) m := add eq_nat_dec k v m.
  Definition idx_msgType_dec: forall (k1 k2: IdxT * RqRs), {k1 = k2} + {k1 <> k2}.
  Proof.
    decide equality.
    - decide equality.
    - apply eq_nat_dec.
  Defined.
  Definition idx_msgType_add {A} (k: IdxT * RqRs) (v: A) m :=
    add idx_msgType_dec k v m.
  Definition idx_idx_dec: forall (k1 k2: IdxT * IdxT), {k1 = k2} + {k1 <> k2}.
  Proof.
    decide equality; apply eq_nat_dec.
  Defined.
  Definition idx_idx_add {A} (k: IdxT * IdxT) (v: A) m :=
    add idx_idx_dec k v m.

  Variable MsgT: Type.
  Variable StateT: Type.

  Record MsgId := { msg_rq : IdxT; (* an object that requests this message *)
                    msg_rs : IdxT; (* an object that responses this message *)
                    msg_rqrs : RqRs;
                    msg_type : MsgT
                  }.

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

  Definition buildMsgId rq rs rr ty :=
    {| msg_rq := rq; msg_rs := rs; msg_rqrs := rr; msg_type := ty |}.

  Inductive PMsg :=
  | Pmsg: forall (msg: MsgId)
                 (precond: StateT -> Prop)
                 (outs: StateT -> list MsgId)
                 (postcond: StateT (* prestate *) ->
                            StateT (* poststate *) -> Prop), PMsg.

  Definition midOf (pmsg: PMsg) :=
    match pmsg with
    | Pmsg msg _ _ _ => msg
    end.

  Definition precondOf (pmsg: PMsg) :=
    match pmsg with
    | Pmsg _ precond _ _ => precond
    end.

  Definition outsOf (pmsg: PMsg) :=
    match pmsg with
    | Pmsg _ _ outs _ => outs
    end.

  Definition postcondOf (pmsg: PMsg) :=
    match pmsg with
    | Pmsg _ _ _ postcond => postcond
    end.

  Record Object :=
    { obj_idx: nat;
      obj_state_init: StateT;
      obj_pmsg_ints: PMsg -> Prop;
      obj_pmsg_exts: PMsg -> Prop
    }.

  Definition Objects := list Object.

  Section Semantics.

    (* Has a record structure in case of more elements are required. *)
    Record ObjectState := { os_st: StateT }.
    
    Definition isPair (m1 m2: MsgId) :=
      (if eq_nat_dec (msg_rq m1) (msg_rq m2) then true else false)
        && (if eq_nat_dec (msg_rs m1) (msg_rs m2) then true else false)
        && (match msg_rqrs m1, msg_rqrs m2 with
            | Rq, Rs => true
            | Rs, Rq => true
            | _, _ => false
            end).

    Definition ObjectStates := Map IdxT ObjectState.

    Definition MsgsFrom :=
      Map (IdxT * RqRs) (* (from, msgType) *) (list MsgId).
    Definition Messages := Map IdxT (* to *) MsgsFrom.

    (* Note that [StepObjExt] takes an arbitrary message [emsg_in] as an input
     * message; the validity for the message is checked at [step], which 
     * employes this definition.
     *)
    Inductive step_obj (obj: Object):
      ObjectState -> MsgsFrom ->
      MsgId (* in *) -> bool (* is_internal *) -> list MsgId (* outs *) ->
      ObjectState -> MsgsFrom -> Prop :=
    | StepObjInt: forall os msgs_from fidx fmsgT fmsg fpmsg fmsgs pos,
        (* always choose the head, which is the oldest *)
        find (fidx, fmsgT) msgs_from = Some (fmsg :: fmsgs) ->

        (* nondeterministically tries to find a predicated message for [fmsg],
         * which satisfies the precondition and postcondition.
         *)
        msgTo fmsg = obj_idx obj ->
        obj_pmsg_ints obj fpmsg -> midOf fpmsg = fmsg ->
        precondOf fpmsg (os_st os) ->
        postcondOf fpmsg (os_st os) pos ->
        (* done! *)
        step_obj obj os msgs_from
                 fmsg true (outsOf fpmsg (os_st os))
                 {| os_st := pos |}
                 (* [fmsg] removed from the queue, which was (fmsg :: fmsgs) *)
                 (idx_msgType_add (fidx, fmsgT) fmsgs msgs_from)
                 
    | StepObjExt: forall os msgs_from emsg epmsg pos,
        (* nondeterministically tries to find a predicated message for [emsg],
         * which satisfies the precondition and postcondition.
         *)
        msgTo emsg = obj_idx obj ->
        obj_pmsg_exts obj epmsg -> midOf epmsg = emsg ->
        precondOf epmsg (os_st os) ->
        postcondOf epmsg (os_st os) pos ->
        (* done! *)
        step_obj obj os msgs_from
                 emsg false (outsOf epmsg (os_st os))
                 {| os_st := pos |}
                 msgs_from.

    Definition distributeMsg (from: IdxT) (msg: MsgId)
               (msgs: Messages): Messages :=
      let to := msgTo msg in
      match find to msgs with
      | Some toMsgs =>
        let added := match toMsgs (from, msg_rqrs msg) with
                       (* should be added last, since the head is the oldest *)
                     | Some fromMsgs => fromMsgs ++ (msg :: nil)
                     | None => msg :: nil
                     end in
        idx_add to (idx_msgType_add (from, msg_rqrs msg) added toMsgs) msgs
      | None =>
        idx_add to (idx_msgType_add (from, msg_rqrs msg) (msg :: nil) (@empty _ _)) msgs
      end.

    Fixpoint distributeMsgs (from: IdxT) (nmsgs: list MsgId)
             (msgs: Messages): Messages :=
      match nmsgs with
      | nil => msgs
      | msg :: nmsgs' => distributeMsgs from nmsgs' (distributeMsg from msg msgs)
      end.

    Definition getIndices (obs: Objects) := map (fun o => obj_idx o) obs.

    Definition isExternal (indices: list nat) (msg: MsgId) :=
      if in_dec eq_nat_dec (msgFrom msg) indices
      then false else true.

    Definition getExt (indices: list nat) (msg: MsgId) :=
      if isExternal indices msg then Some msg else None.
    Definition getExts (indices: list nat) (msgs: list MsgId) :=
      filter (fun pm => isExternal indices pm) msgs.

    Inductive step (obs: Objects) : ObjectStates -> Messages ->
                                    option MsgId (* ext_in *) -> list MsgId (* ext_outs *) ->
                                    ObjectStates -> Messages -> Prop :=
    | Step: forall oss idx (obj: Object) (os: ObjectState)
                   oims msgs_from msg_in is_internal msgs_out pos pmsgs_from,
        In obj obs ->
        obj_idx obj = idx ->
        find idx oss = Some os ->
        find idx oims = Some msgs_from -> 
        step_obj obj os msgs_from msg_in is_internal msgs_out pos pmsgs_from ->
        is_internal = negb (isExternal (getIndices obs) msg_in) ->
        step obs oss oims
             (getExt (getIndices obs) msg_in)
             (getExts (getIndices obs) msgs_out)
             (idx_add idx pos oss)
             (distributeMsgs idx msgs_out (idx_add idx pmsgs_from oims)).

    Definition ocons {A} (oa: option A) (l: list A) :=
      match oa with
      | Some a => a :: l
      | None => l
      end.
    Infix "::>" := ocons (at level 0).

    (* Head is the oldest message. *)
    Inductive steps (obs: Objects) : ObjectStates -> Messages ->
                                     list MsgId (* history *) ->
                                     ObjectStates -> Messages -> Prop :=
    | StepsNil: forall oss oims, steps obs oss oims nil oss oims
    | StepsCons:
        forall oss1 oims1 emsgs oss2 oims2,
          steps obs oss1 oims1 emsgs oss2 oims2 ->
          forall oss3 msg_in msgs_out oims3,
            step obs oss2 oims2 msg_in msgs_out oss3 oims3 ->
            steps obs oss1 oims1 (emsgs ++ msg_in ::> msgs_out) oss3 oims3.

    Fixpoint getObjectStatesInit (obs: Objects) : ObjectStates :=
      match obs with
      | nil => @empty _ _
      | obj :: obs' =>
        idx_add (obj_idx obj)
                {| os_st := obj_state_init obj |}
                (getObjectStatesInit obs')
      end.

    Inductive HistoryOf : Objects -> list MsgId -> Prop :=
    | History:
        forall obs oss oims phst,
          steps obs (getObjectStatesInit obs) (@empty _ _) phst oss oims ->
          HistoryOf obs phst.

    (* A history consisting only of requests and matching responses. *)
    Inductive Complete: list MsgId -> Prop :=
    | CplNil: Complete nil
    | CplAdd:
        forall hst1 hst2 hst3,
          Complete (hst1 ++ hst2 ++ hst3) ->
          forall rq rs,
            isPair rq rs = true ->
            forall chst,
              chst = hst1 ++ rq :: hst2 ++ rs :: hst3 ->
              Complete chst.

    Inductive SubList {A}: list A -> list A -> Prop :=
    | SlNil: SubList nil nil
    | SlAdd: forall l1 l2, SubList l1 l2 -> forall a, SubList (a :: l1) (a :: l2)
    | SlSkip: forall l1 l2, SubList l1 l2 -> forall a, SubList l1 (a :: l2).

    Definition complete (hst chst: list MsgId): Prop :=
      Complete chst /\ SubList chst hst /\
      (* maximal *) forall hst', Complete hst' -> SubList hst' hst -> ~ SubList chst hst'.

    (* An informal definition of "sequential":
     * 1) The first message should be a request
     * 2) A matching response for each request should be right after the request.
     * 3) There might not be a matching response for the last request.
     *)
    Inductive CSequential: list MsgId -> Prop :=
    | CseqNil: CSequential nil
    | CseqAdd:
        forall hst,
          CSequential hst ->
          forall rq rs,
            isPair rq rs = true ->
            forall chst,
              chst = hst ++ rq :: rs :: nil ->
              CSequential chst.

    Inductive Sequential: list MsgId -> Prop :=
    | SeqCompl: forall hst, CSequential hst -> Sequential hst
    | SeqIncom:
        forall hst,
          CSequential hst ->
          forall rq, msg_rqrs rq = Rq ->
                     Sequential (hst ++ rq :: nil).

    (* In message passing system, "object subhistory" and "process subhistory"
     * have exactly the same meaning; here an index "i" indicates a single object.
     * An ambiguity comes when we need to decide whether a req/resp from "i" to "j"
     * belongs to i's or j's subhistory.
     * For requests, j's subhistory contains them.
     * For responses, i's subhistory contains them.
     *)
    Definition isObjectsMsg (obs: list IdxT) (e: MsgId) :=
      (if in_dec idx_msgType_dec (msg_rq e, msg_rqrs e)
                 (map (fun i => (i, Rq)) obs) then true else false)
        || (if in_dec idx_msgType_dec (msg_rs e, msg_rqrs e)
                      (map (fun i => (i, Rs)) obs) then true else false).
    Definition objSubHistory (i: IdxT) (hst: list MsgId) :=
      filter (isObjectsMsg (i :: nil)) hst.

    Definition intHistory (internals: list IdxT) (hst: list MsgId) :=
      filter (isObjectsMsg internals) hst.
    Definition extHistory (internals: list IdxT) (hst: list MsgId) :=
      filter (fun e => negb (isObjectsMsg internals e)) hst.

    (* Two histories are equivalent iff any object subhistories are equal. *)
    Definition Equivalent (hst1 hst2: list MsgId) :=
      forall i, objSubHistory i hst1 = objSubHistory i hst2.

    (* TODO: this is actually not a fully correct definition:
     * 1) [complete] definition is a bit different to the one in original
     * definition, but I think it's enough. Need to confirm whether it's indeed
     * the right definition.
     * 2) Linearizability requires one more condition: any _strict_ transaction
     * orders are preserved by [lhst].
     *)
    Definition Linearizable' (hst lhst: list MsgId) :=
      Sequential lhst /\
      exists chst, complete hst chst /\ Equivalent chst lhst.

    Definition Linearizable (hst: list MsgId) :=
      exists lhst, Linearizable' hst lhst.

    Definition AbsLinear (obs: Objects) (absF: list MsgId -> list MsgId) :=
      forall hst,
        HistoryOf obs hst ->
        exists shst, HistoryOf obs shst /\
                     Linearizable' (absF hst) (absF shst).

    Definition IntLinear (obs: Objects) :=
      AbsLinear obs (intHistory (getIndices obs)).
    Definition ExtLinear (obs: Objects) :=
      AbsLinear obs (extHistory (getIndices obs)).

    (* A system is linear when all possible histories are linearizable. *)
    Definition Linear (obs: Objects) :=
      forall hst,
        HistoryOf obs hst ->
        exists shst, HistoryOf obs shst /\
                     Linearizable' hst shst.

  End Semantics.

  Section Facts.

    Lemma equivalent_refl: forall hst, Equivalent hst hst.
    Proof.
      intros; unfold Equivalent; reflexivity.
    Qed.
    Hint Immediate equivalent_refl.

  End Facts.

End Language.

Hint Immediate equivalent_refl.

