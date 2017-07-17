Require Import Bool List String Peano_dec.
Require Import FnMap.

Set Implicit Arguments.

Open Scope list.

Section Language.

  Definition IdxT := nat.

  (* A message is always either a request or a response. *)
  Inductive MsgType := Rq | Rs.
  
  (** Utilities *)
  Definition idx_add {A} (k: IdxT) (v: A) m := add eq_nat_dec k v m.
  Definition idx_msgType_dec: forall (k1 k2: IdxT * MsgType), {k1 = k2} + {k1 <> k2}.
  Proof.
    decide equality.
    - decide equality.
    - apply eq_nat_dec.
  Defined.
  Definition idx_msgType_add {A} (k: IdxT * MsgType) (v: A) m :=
    add idx_msgType_dec k v m.
  Definition idx_idx_dec: forall (k1 k2: IdxT * IdxT), {k1 = k2} + {k1 <> k2}.
  Proof.
    decide equality; apply eq_nat_dec.
  Defined.
  Definition idx_idx_add {A} (k: IdxT * IdxT) (v: A) m :=
    add idx_idx_dec k v m.

  (* Used in a whole system *)
  Variable MsgT: MsgType -> Type.
  Variable StateT: Type.

  (* [TrsLock] defines a lock for a transaction.
   * Frequently we need to restrict behavior of an object between a certain 
   * request and a following response. [TrsLock] can be used at this moment.
   * The reason for the separation of [TrsLock]s and an object state is for
   * easy verification, especially for the correctness of interleaving
   * (linearizability).
   *)
  Inductive TLock ValueT :=
  | TUnlocked : TLock ValueT
  | TLocked : ValueT -> TLock ValueT.

  (* Big TODO: need to generalize below fixed record type. 
   * When the language is designed and following semantics are defined as a state
   * transition relation, then each lock may be able to have its own type.
   *)
  Record LockElts :=
    { le_idx : IdxT;
      le_val : nat;
      le_flag : bool
    }.
  Definition TrsLock := TLock LockElts. (* TODO: need to generalize *)
  Definition TrsLocks := Map (IdxT (* rq *) * IdxT (* rs *)) TrsLock.

  Section Message.
    Record Msg := { msg_rq : IdxT; (* an object that requests this message *)
                    msg_rs : IdxT; (* an object that responses this message *)
                    msg_type : MsgType;
                    msg_content : MsgT msg_type }.

    Definition msgFrom (msg: Msg) :=
      match msg_type msg with
      | Rq => msg_rq msg
      | Rs => msg_rs msg
      end.

    Definition msgTo (msg: Msg) :=
      match msg_type msg with
      | Rq => msg_rs msg
      | Rs => msg_rq msg
      end.

    Definition buildMsg rq rs {ty} (co: MsgT ty) :=
      {| msg_rq := rq; msg_rs := rs;
         msg_type := ty; msg_content := co |}.

    Inductive PredMsg :=
    | PmRq: forall (msg: Msg)
                   (* Right after the request is sent, this lock is activated. *)
                   (olock: option TrsLock)
                   (* In order to handle the request, [precond] should be satisfied. *)
                   (precond: StateT -> TrsLocks -> Prop), PredMsg
    | PmRs: forall (msg: Msg), PredMsg.

    Definition msgOf (pmsg: PredMsg) :=
      match pmsg with
      | PmRq msg _ _ => msg
      | PmRs msg => msg
      end.

    Definition precondOf (pmsg: PredMsg) :=
      match pmsg with
      | PmRq _ _ precond => precond
      | PmRs _ => fun _ _ => True
      end.

  End Message.

  Section Object.
    
    (* About rules:
     * 1) For output messages, it's more accurate to have a type of [set Msg],
     *    but it's fine if no two messages have the same receiver [msg_to].
     *    This condition should be the part of well-formedness later.
     * 2) A rule doesn't need to give the post [TrsLocks] state, locks are 
     *    automatically held/released by transactions.
     *)
    Definition Rule :=
      Msg -> TrsLocks -> StateT ->
      option (list PredMsg (* messages out *) * StateT (* next state *)).

    Record Object :=
      { obj_idx: nat;
        obj_state_init: StateT;
        obj_rules: list Rule;
      }.

    Definition Objects := list Object.

  End Object.

  Section Semantics.

    Record ObjectState :=
      { os_st: StateT;
        (* list of (request, lock) *)
        os_trs_locks: list (Msg * TrsLock)
      }.
    Fixpoint locksOf (ls: list (Msg * TrsLock)) :=
      match ls with
      | nil => @empty _ _
      | (msg, l) :: ls' => idx_idx_add (msg_rq msg, msg_rs msg) l (locksOf ls')
      end.

    Definition isPair (m1 m2: Msg) :=
      (if eq_nat_dec (msg_rq m1) (msg_rq m2) then true else false)
        && (if eq_nat_dec (msg_rs m1) (msg_rs m2) then true else false)
        && (match msg_type m1, msg_type m2 with
            | Rq, Rs => true
            | Rs, Rq => true
            | _, _ => false
            end).

    Fixpoint addLocks (msgs_out: list PredMsg) (locks: list (Msg * TrsLock)) :=
      match msgs_out with
      | nil => locks
      | msg_out :: msgs_out' =>
        match msg_out with
        | PmRq msg (Some lock) precond => addLocks msgs_out' ((msg, lock) :: locks)
        | _ => addLocks msgs_out' locks
        end
      end.

    Fixpoint removeLock (rs: Msg) (locks: list (Msg * TrsLock)) :=
      match locks with
      | nil => nil
      | (rq, lock) :: locks =>
        if isPair rs rq
        then locks
        else (rq, lock) :: (removeLock rs locks)
      end.

    Definition manageLock (msg_in: PredMsg) (msgs_out: list PredMsg)
               (locks: list (Msg * TrsLock)) (st: StateT) :=
      let alocks := addLocks msgs_out locks in
      match msg_in with
      | PmRs msg => removeLock msg alocks
      | _ => alocks
      end.

    Definition ObjectStates := Map IdxT ObjectState.

    Definition MsgsFrom :=
      Map (IdxT * MsgType) (* (from, msgType) *) (list PredMsg).
    Definition Messages := Map IdxT (* to *) MsgsFrom.

    (* Note that [StepObjExt] takes an arbitrary message [emsg_in] as an input
     * message; the validity for the message is checked at [step], which 
     * employes this definition.
     *)
    Inductive step_obj (obj: Object):
      ObjectState -> MsgsFrom ->
      PredMsg (* in *) -> bool (* is_internal *) -> list PredMsg (* outs *) ->
      ObjectState -> MsgsFrom -> Prop :=
    | StepObjInt: forall os msgs_from fidx fpmsgT fpmsg fpmsgs msgs_out pos rule,
        find (fidx, fpmsgT) msgs_from = Some (fpmsg :: fpmsgs) ->
        msgTo (msgOf fpmsg) = obj_idx obj ->
        precondOf fpmsg (os_st os) (locksOf (os_trs_locks os)) ->
        In rule (obj_rules obj) ->
        rule (msgOf fpmsg) (locksOf (os_trs_locks os)) (os_st os) = Some (msgs_out, pos) ->
        step_obj obj os msgs_from
                 fpmsg true msgs_out
                 {| os_st := pos;
                    os_trs_locks := manageLock fpmsg msgs_out (os_trs_locks os) (os_st os) |}
                 (idx_msgType_add (fidx, fpmsgT) fpmsgs msgs_from)
    | StepObjExt: forall os msgs_from epmsg msgs_out pos rule,
        msgTo (msgOf epmsg) = obj_idx obj ->
        precondOf epmsg (os_st os) (locksOf (os_trs_locks os)) ->
        In rule (obj_rules obj) ->
        rule (msgOf epmsg) (locksOf (os_trs_locks os)) (os_st os) = Some (msgs_out, pos) ->
        step_obj obj os msgs_from
                 epmsg false msgs_out
                 {| os_st := pos;
                    os_trs_locks := manageLock epmsg msgs_out (os_trs_locks os) (os_st os) |}
                 msgs_from.

    Definition distributeMsg (from: IdxT) (pmsg: PredMsg)
               (msgs: Messages): Messages :=
      let msg := msgOf pmsg in
      let to := msgTo msg in
      match find to msgs with
      | Some toMsgs =>
        let added := match toMsgs (from, msg_type msg) with
                     | Some fromMsgs => fromMsgs ++ (pmsg :: nil)
                     | None => pmsg :: nil
                     end in
        idx_add to (idx_msgType_add (from, msg_type msg) added toMsgs) msgs
      | None =>
        idx_add to (idx_msgType_add (from, msg_type msg) (pmsg :: nil) (@empty _ _)) msgs
      end.

    Fixpoint distributeMsgs (from: IdxT) (pmsgs: list PredMsg)
             (msgs: Messages): Messages :=
      match pmsgs with
      | nil => msgs
      | pmsg :: pmsgs' => distributeMsgs from pmsgs' (distributeMsg from pmsg msgs)
      end.

    Definition getIndices (obs: Objects) := map (fun o => obj_idx o) obs.

    Inductive step (obs: Objects) : ObjectStates -> Messages ->
                                    PredMsg (* in *) -> list PredMsg (* outs *) ->
                                    ObjectStates -> Messages -> Prop :=
    | Step: forall oss idx (obj: Object) (os: ObjectState)
                   oims msgs_from msg_in is_internal msgs_out pos pmsgs_from,
        In obj obs ->
        obj_idx obj = idx ->
        find idx oss = Some os ->
        find idx oims = Some msgs_from -> 
        step_obj obj os msgs_from msg_in is_internal msgs_out pos pmsgs_from ->
        is_internal = (if in_dec eq_nat_dec (msgFrom (msgOf msg_in)) (getIndices obs)
                       then true else false) ->
        step obs oss oims
             msg_in msgs_out
             (idx_add idx pos oss)
             (distributeMsgs idx msgs_out (idx_add idx pmsgs_from oims)).

    (* Head is the oldest message. *)
    Inductive steps (obs: Objects) : ObjectStates -> Messages ->
                                     list PredMsg (* history *) ->
                                     ObjectStates -> Messages -> Prop :=
    | StepsNil: forall oss oims, steps obs oss oims nil oss oims
    | StepsCons:
        forall oss1 oims1 emsgs oss2 oims2,
          steps obs oss1 oims1 emsgs oss2 oims2 ->
          forall oss3 msg_in msgs_out oims3,
            step obs oss2 oims2 msg_in msgs_out oss3 oims3 ->
            steps obs oss1 oims1 (emsgs ++ msg_in :: msgs_out) oss3 oims3.

    Fixpoint getObjectStatesInit (obs: Objects) : ObjectStates :=
      match obs with
      | nil => @empty _ _
      | obj :: obs' =>
        idx_add (obj_idx obj)
                {| os_st := obj_state_init obj; os_trs_locks := nil |}
                (getObjectStatesInit obs')
      end.

    Inductive HistoryOf : Objects -> list PredMsg -> Prop :=
    | History:
        forall obs oss oims phst,
          steps obs (getObjectStatesInit obs) (@empty _ _) phst oss oims ->
          HistoryOf obs phst.

    (* A history consisting only of requests and matching responses. *)
    (** TODO: better definition? *)
    Inductive Complete: list Msg -> Prop :=
    | CplNil: Complete nil
    | CplAdd:
        forall hst1 hst2 hst3,
          Complete (hst1 ++ hst2 ++ hst3) ->
          forall rq rs,
            isPair rq rs = true ->
            forall chst,
              chst = hst1 ++ rq :: hst2 ++ rs :: hst3 ->
              Complete chst.

    (* An informal definition of "sequential":
     * 1) The first message should be a request
     * 2) A matching response for each request should be right after the request.
     * 3) There might not be a matching response for the last request.
     *)
    Inductive CSequential: list Msg -> Prop :=
    | CseqNil: CSequential nil
    | CseqAdd:
        forall hst,
          CSequential hst ->
          forall rq rs,
            isPair rq rs = true ->
            forall chst,
              chst = hst ++ rq :: rs :: nil ->
              CSequential chst.

    Inductive Sequential: list Msg -> Prop :=
    | SeqCompl: forall hst, CSequential hst -> Sequential hst
    | SeqIncom:
        forall hst,
          CSequential hst ->
          forall rq, msg_type rq = Rq ->
                     Sequential (hst ++ rq :: nil).

    (* In message passing system, "object subhistory" and "process subhistory"
     * have exactly the same meaning; here an index "i" indicates a single object.
     * An ambiguity comes when we need to decide whether a req/resp from "i" to "j"
     * belongs to i's or j's subhistory.
     * For requests, j's subhistory contains them.
     * For responses, i's subhistory contains them.
     *)
    Definition isObjectsMsg (obs: list IdxT) (e: Msg) :=
      (if in_dec idx_msgType_dec (msg_rq e, msg_type e)
                 (map (fun i => (i, Rq)) obs) then true else false)
        || (if in_dec idx_msgType_dec (msg_rs e, msg_type e)
                      (map (fun i => (i, Rs)) obs) then true else false).
    Definition objSubHistory (i: IdxT) (hst: list Msg) :=
      filter (isObjectsMsg (i :: nil)) hst.

    Definition intHistory (internals: list IdxT) (hst: list Msg) :=
      filter (isObjectsMsg internals) hst.
    Definition extHistory (internals: list IdxT) (hst: list Msg) :=
      filter (fun e => negb (isObjectsMsg internals e)) hst.

    (* Two histories are equivalent iff any object subhistories are equal. *)
    Definition Equivalent (hst1 hst2: list Msg) :=
      forall i, objSubHistory i hst1 = objSubHistory i hst2.

    (* TODO: this is actually not a fully correct definition:
     * 1) Instead of [Equivalent hst lhst], we need [Equivalent (complete hst) lhst]
     * 2) Linearizability requires one more condition: any _strict_ transaction
     *    orders are preserved by [lhst].
     *)
    Definition Linearizable' (hst lhst: list Msg) :=
      Sequential lhst /\ Equivalent hst lhst.

    Definition Linearizable (hst: list Msg) :=
      exists lhst, Linearizable' hst lhst.

    Definition AbsLinear (obs: Objects) (absF: list Msg -> list Msg) :=
      forall hst,
        HistoryOf obs hst ->
        exists shst, HistoryOf obs shst /\
                     Linearizable' (absF (map msgOf hst)) (absF (map msgOf shst)).

    Definition IntLinear (obs: Objects) :=
      AbsLinear obs (intHistory (getIndices obs)).
    Definition ExtLinear (obs: Objects) :=
      AbsLinear obs (extHistory (getIndices obs)).

    (* A system is linear when all possible histories are linearizable. *)
    Definition Linear (obs: Objects) :=
      forall hst,
        HistoryOf obs hst ->
        exists shst, HistoryOf obs shst /\
                     Linearizable' (map msgOf hst) (map msgOf shst).

  End Semantics.

  Section Facts.

    Lemma equivalent_refl: forall hst, Equivalent hst hst.
    Proof. intros; unfold Equivalent; reflexivity. Qed.
    Hint Immediate equivalent_refl.

  End Facts.

End Language.

Hint Immediate equivalent_refl.

