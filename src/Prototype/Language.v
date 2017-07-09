Require Import Bool List String Peano_dec.
Require Import FnMap.

Set Implicit Arguments.

Open Scope list.

Section Language.

  Definition IdxT := nat.

  (* A message is always either a request or a response.
   * A request indicates a start of a transaction.
   * A corresponding response indicates the end of the transaction.
   *)
  Variable MsgT: Type.
  Inductive MsgType := Req | Resp.
  Record Msg := { msg_type : MsgType;
                  msg_from : IdxT;
                  msg_to : IdxT;
                  msg_content : MsgT }.
  Definition buildMsg ty fr to co :=
    {| msg_type := ty; msg_from := fr; msg_to := to; msg_content := co |}.
  
  Section Syntax.

    Section Object.
      Variable StateT: Type.

      (* For output messages, it's more robust to have a type of [set Msg],
       * but it's fine if no two messages have the same receiver [msg_to].
       * It's worth considering this condition being the part of well-formedness.
       *)
      Definition CmdT :=
        StateT -> option (list Msg (* messages out *) * StateT (* next state *)).
      Definition RuleT := Msg -> CmdT.

      Record Object :=
        { obj_idx: nat;
          obj_state_init: StateT;
          obj_rules: list RuleT;
        }.

    End Object.

    Definition Objects := list { st : Type & Object st }.

  End Syntax.

  Section Semantics.

    Record ObjectState StateT :=
      { (* os_obj: Object StateT; *)
        os_state: StateT
      }.

    Definition ObjectStates :=
      Map IdxT { StateT : Type & ObjectState StateT }.

    Definition MsgsFrom := Map (IdxT * MsgType) (* (from, msgType) *) (list Msg).
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

    (* Return the result handled meaningfully first by a rule. *)
    Fixpoint step_rule {StateT} (rules: list (RuleT StateT))
             (imsg: Msg) (st: StateT) :=
      match rules with
      | nil => None
      | r :: rules' =>
        match r imsg st with 
        | Some mst => Some mst
        | None => step_rule rules' imsg st
        end
      end.

    (* Note that [StepObjExt] takes an arbitrary message [emsg_in] as an input
     * message; the validity for the message is checked at [step], which 
     * employes this definition.
     *)
    Inductive step_obj {StateT} (obj: Object StateT):
      ObjectState StateT -> MsgsFrom ->
      Msg (* in *) -> bool (* is_internal *) -> list Msg (* outs *) ->
      ObjectState StateT -> MsgsFrom -> Prop :=
    | StepObjInt: forall os msgs_from fidx fmsgT fmsg fmsgs msgs_out pos,
        step_rule (obj_rules obj) fmsg (os_state os) =
        Some (msgs_out, pos) ->
        find (fidx, fmsgT) msgs_from = Some (fmsg :: fmsgs) ->
        step_obj obj os msgs_from
                 fmsg true msgs_out
                 {| os_state := pos |}
                 (idx_msgType_add (fidx, fmsgT) fmsgs msgs_from)
    | StepObjExt: forall os msgs_from emsg_in msgs_out pos,
        step_rule (obj_rules obj) emsg_in (os_state os) =
        Some (msgs_out, pos) ->
        step_obj obj os msgs_from
                 emsg_in false msgs_out
                 {| os_state := pos |}
                 msgs_from.

    Fixpoint distr_msgs (from: IdxT) (to: list Msg)
             (msgs: Messages): Messages :=
      match to with
      | nil => msgs
      | msg :: to' =>
        match find (msg_to msg) msgs with
        | Some toMsgs =>
          let added := match toMsgs (from, msg_type msg) with
                       | Some fromMsgs => fromMsgs ++ (msg :: nil)
                       | None => msg :: nil
                       end in
          idx_add (msg_to msg)
                  (idx_msgType_add (from, msg_type msg) added toMsgs)
                  msgs
        | None =>
          idx_add (msg_to msg)
                  (idx_msgType_add (from, msg_type msg) (msg :: nil) (@empty _ _))
                  msgs
        end
      end.

    Definition getIndices (obs: Objects) :=
      map (fun o => obj_idx (projT2 o)) obs.

    Inductive step (obs: Objects) : ObjectStates -> Messages ->
                                    Msg (* in *) -> list Msg (* outs *) ->
                                    ObjectStates -> Messages -> Prop :=
    | Step: forall oss idx {StateT} (obj: Object StateT) (os: ObjectState StateT)
                   oims msgs_from msg_in is_internal msgs_out pos pmsgs_from,
        In (existT _ _ obj) obs ->
        obj_idx obj = idx ->
        find idx oss = Some (existT _ _ os) ->
        find idx oims = Some msgs_from -> 
        step_obj obj os msgs_from msg_in is_internal msgs_out pos pmsgs_from ->
        is_internal = (if in_dec eq_nat_dec (msg_to msg_in) (getIndices obs)
                       then true else false) ->
        step obs oss oims
             msg_in msgs_out
             (idx_add idx (existT _ _ pos) oss)
             (distr_msgs idx msgs_out (idx_add idx pmsgs_from oims)).

    Inductive steps (obs: Objects) : ObjectStates -> Messages ->
                                     list Msg (* history *) ->
                                     ObjectStates -> Messages -> Prop :=
    | StepsNil: forall oss oims, steps obs oss oims nil oss oims
    | StepsCons:
        forall oss1 oims1 emsgs oss2 oims2,
          steps obs oss1 oims1 emsgs oss2 oims2 ->
          forall oss3 msg_in msgs_out oims3,
            step obs oss2 oims2 msg_in msgs_out oss3 oims3 ->
            steps obs oss1 oims1 (emsgs ++ msg_in :: msgs_out) oss3 oims3.

    Definition getObjectStateInit {StateT} (obj: Object StateT) :=
      {| os_state := obj_state_init obj |}.
    Fixpoint getObjectStatesInit (obs: Objects) : ObjectStates :=
      match obs with
      | nil => @empty _ _
      | obj :: obs' =>
        idx_add (obj_idx (projT2 obj))
                (existT _ _ (getObjectStateInit (projT2 obj)))
                (getObjectStatesInit obs')
      end.

    Definition HistoryOf (obs: Objects) (hst: list Msg) :=
      exists oss oims, steps obs (getObjectStatesInit obs) (@empty _ _) hst oss oims.

    (* A maximum subsequence of H consisting only of requests and matching responses. *)
    (* Should be a fancier implementation *)
    Fixpoint complete' (hst: list Msg) : (list Msg * Map (IdxT (* request_from *) *
                                                          IdxT (* request_to *)) nat) :=
      match hst with
      | nil => (nil, @empty _ _)
      | msg :: hst' =>
        let (chst, rs) := complete' hst' in
        if msg_type msg then (* request *)
          match find (msg_from msg, msg_to msg) rs with
          | Some (S n) => (msg :: chst, idx_idx_add (msg_from msg, msg_to msg) n rs)
          | _ => (chst, rs)
          end
        else (* response *)
          (msg :: chst, idx_idx_add (msg_to msg, msg_from msg)
                                    (match find (msg_to msg, msg_from msg) rs with
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
    Fixpoint Sequential' (hst: list Msg) (oi: option (IdxT (* request_from *) *
                                                      IdxT (* request_to *))) :=
      match hst with
      | nil => True
      | msg :: hst' =>
        match oi with
        | Some (from, to) => msg_to msg = from /\ msg_from msg = to /\ msg_type msg = Resp /\
                             Sequential' hst' None
        | None => msg_type msg = Req /\ Sequential' hst' (Some (msg_from msg, msg_to msg))
        end
      end.
    Definition Sequential (hst: list Msg) := Sequential' hst None.

    (* In message passing system, "object subhistory" and "process subhistory"
     * have exactly the same meaning; here an index "i" indicates a single object.
     * An ambiguity comes when we need to decide whether a req/resp from "i" to "j"
     * belongs to i's or j's subhistory.
     * For requests, j's subhistory contains them.
     * For responses, i's subhistory contains them.
     *)
    Definition isObjectsMsg (obs: list IdxT) (e: Msg) :=
      (if in_dec idx_msgType_dec (msg_to e, msg_type e)
                 (map (fun i => (i, Req)) obs) then true else false)
        || (if in_dec idx_msgType_dec (msg_from e, msg_type e)
                      (map (fun i => (i, Resp)) obs) then true else false).
    Definition objSubHistory (i: IdxT) (hst: list Msg) :=
      filter (isObjectsMsg (i :: nil)) hst.

    Definition intHistory (internals: list IdxT) (hst: list Msg) :=
      filter (isObjectsMsg internals) hst.
    Definition extHistory (internals: list IdxT) (hst: list Msg) :=
      filter (fun e => negb (isObjectsMsg internals e)) hst.

    (* Two histories are equivalent iff any subhistories are equal. *)
    Definition Equivalent (hst1 hst2: list Msg) :=
      forall i, objSubHistory i hst1 = objSubHistory i hst2.

    Definition Linearlizable' (hst lhst: list Msg) :=
      Sequential lhst /\ Equivalent (complete hst) lhst.

    Definition Linearlizable (hst: list Msg) :=
      exists lhst, Linearlizable' hst lhst.

    Definition AbsLinear (obs: Objects) (absF: list Msg -> list Msg) :=
      forall hst,
        HistoryOf obs hst ->
        exists shst, HistoryOf obs shst /\
                     Linearlizable' (absF hst) (absF shst).

    Definition IntLinear (obs: Objects) :=
      AbsLinear obs (intHistory (getIndices obs)).
    Definition ExtLinear (obs: Objects) :=
      AbsLinear obs (extHistory (getIndices obs)).

    (* A system is linear when all possible histories are linearlizable. *)
    Definition Linear (obs: Objects) :=
      forall hst,
        HistoryOf obs hst ->
        exists shst, HistoryOf obs shst /\ Linearlizable' hst shst.

  End Semantics.

  Section Facts.

    Lemma equivalent_refl: forall hst, Equivalent hst hst.
    Proof. intros; unfold Equivalent; reflexivity. Qed.
    Hint Immediate equivalent_refl.

    Lemma sequential_complete: forall hst, Sequential hst -> Sequential (complete hst).
    Proof.
    Admitted.

    Lemma intHistory_complete_comm:
      forall hst internals,
        intHistory internals (complete hst) = complete (intHistory internals hst).
    Proof.
    Admitted.
    
    Theorem extLinear_local:
      forall obs,
        (forall obj, In obj obs -> IntLinear (obj :: nil)) ->
        ExtLinear obs.
    Proof.
    Admitted.

  End Facts.

End Language.

Hint Immediate equivalent_refl.

