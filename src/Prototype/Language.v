Require Import Bool List String Peano_dec.
Require Import FnMap.

Set Implicit Arguments.

Open Scope list.

Section Language.

  Definition IdxT := nat.

  (* A message is always either a request or a response. *)
  Inductive MsgType := Rq | Rs.

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
  Definition TrsLock := { valT : Type & TLock valT }.
  Definition TrsLocks := list { valT : Type & TLock valT }.

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

    Record PredMsg := { pm_msg : Msg;
                        pm_trs_lock : TrsLock;
                        pm_rs_precond : StateT -> Prop;
                      }.

  End Message.

  Section Object.
    
    (* For output messages, it's more accurate to have a type of [set Msg],
     * but it's fine if no two messages have the same receiver [msg_to].
     * This condition should be the part of well-formedness later.
     *)
    Record Rule :=
      { rule_precond_rqs : list PredMsg -> Prop;
        rule_body : Msg -> StateT ->
                    option (list PredMsg (* messages out *) * StateT (* next state *))
      }.

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
        os_rqs: list PredMsg;
      }.

    Definition isPair (m1 m2: Msg) :=
      (if eq_nat_dec (msg_rq m1) (msg_rq m2) then true else false)
        && (if eq_nat_dec (msg_rs m1) (msg_rs m2) then true else false)
        && (match msg_type m1, msg_type m2 with
            | Rq, Rs => true
            | Rs, Rq => true
            | _, _ => false
            end).

    Fixpoint removeRq (rs: PredMsg) (rqs: list PredMsg) :=
      match rqs with
      | nil => nil
      | rq :: rqs =>
        if isPair (pm_msg rs) (pm_msg rq) then rqs else rq :: (removeRq rs rqs)
      end.

    Definition ObjectStates := Map IdxT ObjectState.

    Definition MsgsFrom :=
      Map (IdxT * MsgType) (* (from, msgType) *) (list PredMsg).
    Definition Messages := Map IdxT (* to *) MsgsFrom.

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
        msgTo (pm_msg fpmsg) = obj_idx obj ->
        pm_rs_precond fpmsg (os_st os) ->
        In rule (obj_rules obj) ->
        rule_precond_rqs rule (os_rqs os) ->
        rule_body rule (pm_msg fpmsg) (os_st os) = Some (msgs_out, pos) ->
        step_obj obj os msgs_from
                 fpmsg true msgs_out
                 {| os_st := pos; os_rqs := removeRq fpmsg (os_rqs os) |}
                 (idx_msgType_add (fidx, fpmsgT) fpmsgs msgs_from)
    | StepObjExt: forall os msgs_from epmsg msgs_out pos rule,
        msgTo (pm_msg epmsg) = obj_idx obj ->
        pm_rs_precond epmsg (os_st os) ->
        In rule (obj_rules obj) ->
        rule_precond_rqs rule (os_rqs os) -> 
        rule_body rule (pm_msg epmsg) (os_st os) = Some (msgs_out, pos) ->
        step_obj obj os msgs_from
                 epmsg false msgs_out
                 {| os_st := pos; os_rqs := removeRq epmsg (os_rqs os) |}
                 msgs_from.

    Definition distributeMsg (from: IdxT) (pmsg: PredMsg)
               (msgs: Messages): Messages :=
      let msg := pm_msg pmsg in
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
        is_internal = (if in_dec eq_nat_dec (msgFrom (pm_msg msg_in)) (getIndices obs)
                       then true else false) ->
        step obs oss oims
             msg_in msgs_out
             (idx_add idx pos oss)
             (distributeMsgs idx msgs_out (idx_add idx pmsgs_from oims)).

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
                {| os_st := obj_state_init obj; os_rqs := nil |}
                (getObjectStatesInit obs')
      end.

    Inductive HistoryOf : Objects -> list Msg -> Prop :=
    | History:
        forall obs oss oims phst,
          steps obs (getObjectStatesInit obs) (@empty _ _) phst oss oims ->
          HistoryOf obs (map pm_msg phst).

    (* A maximum subsequence of H consisting only of requests and matching responses. *)
    (** TODO: Should be a fancier implementation *)
    Fixpoint complete' (hst: list Msg) : (list Msg * Map (IdxT (* request_from *) *
                                                          IdxT (* request_to *)) nat) :=
      match hst with
      | nil => (nil, @empty _ _)
      | msg :: hst' =>
        let (chst, rs) := complete' hst' in
        if msg_type msg then (* request *)
          match find (msgFrom msg, msgTo msg) rs with
          | Some (S n) => (msg :: chst, idx_idx_add (msgFrom msg, msgTo msg) n rs)
          | _ => (chst, rs)
          end
        else (* response *)
          (msg :: chst, idx_idx_add (msgTo msg, msgFrom msg)
                                    (match find (msgTo msg, msgFrom msg) rs with
                                     | Some n => S n
                                     | None => 1
                                     end) rs)
      end.

    Definition complete (hst: list Msg) := fst (complete' hst).
    Definition Complete (hst: list Msg) := hst = complete hst.

    (* An informal definition of "sequential":
     * 1) The first message should be a request
     * 2) A matching response for each request should be right after the request.
     * 3) There might not be a matching response for the last request.
     *)
    Fixpoint Sequential' (hst: list Msg)
             (pre post: option (IdxT (* requester *) *
                                IdxT (* responder *))) :=
      match hst with
      | nil => pre = post
      | msg :: hst' =>
        match pre with
        | Some (rq, rs) => msg_rq msg = rq /\ msg_rs msg = rs /\ msg_type msg = Rs /\
                           Sequential' hst' None post
        | None => msg_type msg = Rq /\ Sequential' hst' (Some (msg_rq msg, msg_rs msg)) post
        end
      end.
    Definition Sequential (hst: list Msg) := exists post, Sequential' hst None post.

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

    (* Two histories are equivalent iff any subhistories are equal. *)
    Definition Equivalent (hst1 hst2: list Msg) :=
      forall i, objSubHistory i hst1 = objSubHistory i hst2.

    Definition Linearizable' (hst lhst: list Msg) :=
      Sequential lhst /\ Equivalent (complete hst) lhst.

    Definition Linearizable (hst: list Msg) :=
      exists lhst, Linearizable' hst lhst.

    Definition AbsLinear (obs: Objects) (absF: list Msg -> list Msg) :=
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
        exists shst, HistoryOf obs shst /\ Linearizable' hst shst.

  End Semantics.

  Section Facts.

    Lemma equivalent_refl: forall hst, Equivalent hst hst.
    Proof. intros; unfold Equivalent; reflexivity. Qed.
    Hint Immediate equivalent_refl.

    Lemma sequential_app:
      forall hst1 p1 p2,
        Sequential' hst1 p1 p2 ->
        forall hst2 p3,
          Sequential' hst2 p2 p3 ->
          Sequential' (hst1 ++ hst2) p1 p3.
    Proof.
      induction hst1; simpl; intros; subst; auto.
      destruct p1 as [[ ]|].
      - destruct H as [? [? [? ?]]]; subst.
        repeat split; eauto.
      - destruct H.
        repeat split; eauto.
    Qed.

    Lemma sequential_complete: forall hst, Sequential hst -> Sequential (complete hst).
    Proof.
    Admitted.

    Lemma intHistory_app:
      forall internals (hst1 hst2: list Msg),
        intHistory internals (hst1 ++ hst2) =
        intHistory internals hst1 ++ intHistory internals hst2.
    Proof.
      induction hst1; simpl; intros; auto.
      destruct (isObjectsMsg internals a); simpl; auto.
      f_equal; auto.
    Qed.

    Lemma intHistory_complete_comm:
      forall hst internals,
        intHistory internals (complete hst) = complete (intHistory internals hst).
    Proof.
    Admitted.

    Lemma complete_sequential_app:
      forall seq hst,
        Sequential' seq None None ->
        complete (seq ++ hst) = seq ++ complete hst.
    Proof.
    Admitted.

    Lemma linearizable_sequential_app:
      forall hst lhst,
        Linearizable' hst lhst ->
        forall seq,
          Sequential' seq None None ->
          Linearizable' (seq ++ hst) (seq ++ lhst).
    Proof.
      unfold Linearizable', Sequential; intros.
      destruct H as [[post ?] ?].
      split.
      - eexists; eapply sequential_app; eauto.
      - rewrite complete_sequential_app by assumption.
    Admitted.

    Lemma linearizable_sequential_closed:
      forall seq hst,
        Sequential' seq None None ->
        Linearizable hst ->
        Linearizable (seq ++ hst).
    Proof.
      unfold Linearizable; intros.
      destruct H0 as [lhst ?].
      exists (seq ++ lhst).
      apply linearizable_sequential_app; auto.
    Qed.

  End Facts.

End Language.

Hint Immediate equivalent_refl.

